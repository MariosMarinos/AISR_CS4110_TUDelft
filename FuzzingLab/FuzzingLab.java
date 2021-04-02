package nl.tudelft.instrumentation.fuzzing;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintWriter;
import java.util.*;
import java.util.Map.Entry;

import org.apache.commons.lang3.StringUtils;

/**
 * You should write your own solution using this class.
 */
public class FuzzingLab {

    private static final Random RANDOM = new Random();
    private static final Map<Integer, Branch> FOUND_BRANCHES = new HashMap<>();
    private static final Map<String, InputSample> FOUND_ERROR_MAP = new HashMap<>();
    private static final Map<ArrayList<String>, Integer> FOUND_BRANCHES_TRACE = new HashMap<>();
    static long startTime = System.currentTimeMillis();
    static int traceLength = 10;
    static int constant_K = 1;

    static int currentConfiguration = 0;
    static int currentRun = 0;
    static int iteration = 0;

    static final Object[][] CONFIGS = new Object[][] { //
            new Object[] { "random_search", false, 0 }, //
            new Object[] { "hillclimb_0.1", true, 0.1 }, //
            new Object[] { "hillclimb_0.5", true, 0.5 }, //
            new Object[] { "hillclimb_0.9", true, 0.9 }, //
    };

    /**
     * Settings that are specific for this run.
     */
    static int averageOverRuns = 1;
    // input traces fed to the problem.
    static int iterations = 2048 * 8;
    static int[] uniqueBranchCount = new int[iterations];
    static int[] uniqueErrorCount = new int[iterations];

    static File fileBranch;
    static File fileErrors;
    static PrintWriter logger;

    static {
        // build a file to write all important data to,
        // allows for building graphs etc later
        final File folder = new File("./run_outputs/");
        folder.mkdirs();

        // find the first free problem id
        int i = 0;
        for (;; i++) {
            final File f = new File(folder, "datalog_" + i + ".txt");
            if (!f.exists())
                break;
        }

        try {
            fileBranch = new File(folder, "branches_" + i + ".tsv");
            fileErrors = new File(folder, "errors_" + i + ".tsv");
            logger = new PrintWriter(new File(folder, "datalog_" + i + ".txt"));
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            System.exit(0);
        }
    }

    private static void save(File f, int[] counter) {
        try {
            // first read it into memory, because we are appending here
            final List<String> lines = new ArrayList<>();
            if (f.exists()) {
                try (Scanner sc = new Scanner(f)) {
                    while (sc.hasNextLine()) {
                        lines.add(sc.nextLine());
                    }
                }
            } else {
                // fill with empty for first run
                for (int i = 0; i < (iterations + 1); i++)
                    lines.add("");
            }
            final Iterator<String> it = lines.iterator();

            System.out.println("Saving to [" + lines.size() + "] " + f.getAbsolutePath());
            // "hillclimb_0.05", true, 0.05
            final String name = (String) CONFIGS[currentConfiguration][0];
            try (PrintWriter writeTo = new PrintWriter(f)) {

                writeTo.println(it.next() + "\t" + name);

                for (int i = 0; i < iterations; i++) {
                    writeTo.println(it.next() + "\t" + (counter[i] / averageOverRuns));
                }
            }
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        }
    }

    // this is called for an error in our fuzzer, not for an error in the problems
    private static int error(String error) {
        System.out.println("[ERROR] " + error);
        System.exit(0);
        return 0;
    }

    /**
     * Write your solution that specifies what should happen when a new branch has
     * been found.
     */
    @SuppressWarnings("deprecation")
    static double calculateBranchDistance(MyVar condition) {

        final MyVar left = eval(condition.left);
        final MyVar right = eval(condition.right);

        if (condition.type == 1) {
            // we have a simple boolean value
            return condition.value ? 0 : 1;

        } else if (condition.type == 5) { // type 5 is two-sided operator

            // predicates
            if (condition.operator.equals("&&")) {
                return normalize(calculateBranchDistance(left))//
                        + normalize(calculateBranchDistance(right));

            } else if (condition.operator.equals("||")) {
                return Math.min(//
                        normalize(calculateBranchDistance(left)), //
                        normalize(calculateBranchDistance(right)));

            } else if (condition.operator.equals("==")) {

                // either integer comparison
                if (left.type == 2 && right.type == 2)
                    return Math.abs(left.int_value - right.int_value);

                    // or boolean comparison
                else if (left.type == 1 && right.type == 1)
                    return (left.value == right.value) ? 0 : 1;

                    // or string comparison
                else if (left.type == 3 && right.type == 3)
                    return StringUtils.getLevenshteinDistance(left.str_value, right.str_value);

                    // else we don't know
                else
                    return error("Unable to compare types " + left.type + " and " + right.type);

            } else if (condition.operator.equals("!=")) {
                // integer comparison
                if (left.type == 2 && right.type == 2) {
                    return (left.int_value != right.int_value) ? 0 : 1;

                    // boolean comparison
                } else if (left.type == 1 && right.type == 1) {
                    return (left.value != right.value) ? 0 : 1;

                } else
                    return error("Unable to compare types [!=] " + left.type + " and " + right.type);

            } else if (condition.operator.equals("<")) {

                // only supported for integers
                if (left.type == 2 && right.type == 2)
                    return (left.int_value < right.int_value) ? 0 : left.int_value - right.int_value + constant_K;

                else
                    return error("Unable to compare types [<] " + left.type + " and " + right.type);

            } else if (condition.operator.equals(">")) {

                // only supported for integers
                if (left.type == 2 && right.type == 2)
                    return (left.int_value > right.int_value) ? 0 : right.int_value - left.int_value + constant_K;

                else
                    return error("Unable to compare types [>] " + left.type + " and " + right.type);

            }

            else if (condition.operator.equals("<=")) {

                // only supported for integers
                if (left.type == 2 && right.type == 2)
                    return (left.int_value <= right.int_value) ? 0 : left.int_value - right.int_value;

                else
                    return error("Unable to compare types [<=] " + left.type + " and " + right.type);

            } else if (condition.operator.equals(">=")) {

                // only supported for integers
                if (left.type == 2 && right.type == 2)
                    return (left.int_value >= right.int_value) ? 0 : right.int_value - left.int_value;

                else
                    return error("Unable to compare types [>=] " + left.type + " and " + right.type);

            } else
                return error("Unknown combination operator " + condition.operator);
        } else
            return error("Unknown type " + condition.type);
    }

    private static MyVar eval(MyVar var) {
        if (var == null)
            return null;

        // unary operators can often simply be evaluated to their actual value
        if (var.type == 4) {
            final MyVar on = var.left;
            // integer minus
            if (var.operator.equals("-") && on.type == 2) {
                return new MyVar(-1 * on.int_value);
            } else
                error("Cannot evaluate operator " + var.operator + " on type " + on.type);
        }
        return var;
    }

    private static double normalize(double d) {
        return d / (d + 1.0);
    }

    // IMPORTANT; "else" statements do not seem to be used in RERS, so no need to also check the false branches
    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr){
        // do something useful
        final double distance = calculateBranchDistance(condition);
        // calculate the total distance of each sample that we use.
        currentSample.DistanceSum += distance;
        // verify this is correct in all cases
        if (value && distance != 0)
            error("Value of condition was TRUE but distance was " + distance);
        if (!value && distance == 0)
            error("Value of condition was FALSE but distance was 0");

        // lookup this branch in the memory
        Branch branch = FOUND_BRANCHES.get(line_nr);
        if (branch == null) {
            FOUND_BRANCHES.put(line_nr, branch = new Branch());
            int count = FOUND_BRANCHES_TRACE.containsKey(currentSample.input) ? FOUND_BRANCHES_TRACE.get(currentSample.input) : 0;
            FOUND_BRANCHES_TRACE.put(currentSample.input, count + 1);
        }
        // check if with the current sample and current branch distance sum, we improve the known one
        branch.checkIfBest(currentSample, distance);
    }

    /**
     * Method for fuzzing new inputs for a program.
     *
     * @param inputSymbols the inputSymbols
     * @return a fuzzed input
     */

    static InputSample currentSample;
    static ArrayList<InputSample> allSamplesUsed = new ArrayList<InputSample>();
    /*
     * stage 0 - nothing initialized yet, initialize a first random population
     * stage 1 - running
     */
    static String fuzz(String[] inputSymbols) {

        if (currentSample == null) {
            currentSample = generateRandomTrace(inputSymbols);
            allSamplesUsed.add(currentSample);
        }

        if (!currentSample.hasNext()) {
            final boolean hillclimb = (boolean) CONFIGS[currentConfiguration][1];
            if (hillclimb) {
                // select which branch we are aiming to improve the branch distance for
                 final Branch worst = nextBranch();
                // if we have no bad branch, or with random probability, explore via a random value
                if (RANDOM.nextDouble() < 0.2) {
                    // explore, use a random sample
                    currentSample = generateRandomTrace(inputSymbols);
                    allSamplesUsed.add(currentSample);
                } else {
                    currentSample = worst.bestSample.permutation(inputSymbols);
                    allSamplesUsed.add(currentSample);
                }
            } else {
                currentSample = generateRandomTrace(inputSymbols);
                allSamplesUsed.add(currentSample);
            }

            System.out.println("Selected new sample FOUND [" //
                    + FOUND_BRANCHES.size() + "] ERRORS [" + FOUND_ERROR_MAP.size() + "]");

            uniqueBranchCount[iteration] += FOUND_BRANCHES.size();
            uniqueErrorCount[iteration] += FOUND_ERROR_MAP.size();
            iteration += 1;

            if (iteration >= iterations) {

                // go to the next 'run'
                final long currentTime = System.currentTimeMillis();

                final long took = currentTime - startTime;
                logger.println("Run on configuration " + currentConfiguration + //
                        " " + Arrays.toString(CONFIGS[currentConfiguration]) + " took " + took //
                        + " millisecond(s) and found " + FOUND_ERROR_MAP.size() + " error(s) and "
                        + FOUND_BRANCHES.size() //
                        + " branch(es).");
                for (Entry<String, InputSample> error : FOUND_ERROR_MAP.entrySet()) {
                    logger.println("\t - Error " + error.getKey() + " caused by " + error.getValue().input);
                }
                //get the highest branch coverage input trace that we have.
                List<List<String>> minKey = new ArrayList<List<String>>();
                List<List<String>> maxKey = new ArrayList<List<String>>();
                Integer maxValue=Integer.MIN_VALUE;
                float minValue=Float.MAX_VALUE;
                for (Map.Entry<ArrayList<String>, Integer> entry : FOUND_BRANCHES_TRACE.entrySet()) {
                    Integer value = entry.getValue();
                    List<String> key = entry.getKey();
                    if(maxValue<value){
                        maxValue =  value;
                        maxKey.clear();
                        maxKey.add(key);
                    } else if(maxValue.equals(value)){
                        maxKey.add(key);
                    }
                    // System.out.println("Key = " + entry.getKey() + ", Value = " + entry.getValue());
                }
                System.out.println("Trace(s) which achieved the highest branch coverage:" + maxKey);

                findMinBranchDistanceTrace(minKey, minValue);
                System.out.println("Trace(s) which achieved the lowest branch distance:" + minKey);
                logger.flush();
                FOUND_BRANCHES_TRACE.clear();
                FOUND_BRANCHES.clear();
                FOUND_ERROR_MAP.clear();
                startTime = currentTime;
                currentSample = generateRandomTrace(inputSymbols);
                iteration = 0;
                currentRun += 1;
                if (currentRun >= averageOverRuns) {
                    System.out.println("Done, writing data to file...");
                    save(fileBranch, uniqueBranchCount);
                    save(fileErrors, uniqueErrorCount);


                    // moving to the next configuration
                    currentRun = 0;
                    currentConfiguration++;
                    uniqueBranchCount = new int[iterations];
                    uniqueErrorCount = new int[iterations];
                    if (currentConfiguration == CONFIGS.length) {
                        System.out.println("Done!");
                        System.exit(0);
                    }
                }
            }
        }
        return currentSample.next();
    }


    private static void findMinBranchDistanceTrace(List<List<String>> minKey, Float minValue) {
        for (InputSample sample : allSamplesUsed) {
            float value = sample.getDistanceSum();
            if(minValue >value){
                minValue = value;
                minKey.clear();
                minKey.add(sample.input);
            } else if(minValue.equals(value)){
                minKey.add(sample.input);
            }
        }
    }

    private static Branch nextBranch() {
        // grab a random branch that has not been triggered yet and try to improve it
        // if a branch has 0 branch distance it means that it was triggered both true and false.
        final List<Branch> all = new ArrayList<>(FOUND_BRANCHES.values());
        final Iterator<Branch> it = all.iterator();
        // with 50% we get a branch distance of 0 to see if there are further branches to discover
        // otherwise we remove the 0's and get the minimum of the other branches to improve it.
        if (RANDOM.nextDouble() < 0.5) {
            while (it.hasNext()) {
                if (it.next().bestBranchDistanceSum == 0) {
                    it.remove();
                }
            }
        }
        // after removing all the 0's we need to get the minimum
        //
        double min = Float.MAX_VALUE;
        Branch bestBranch = null;
        for (Branch branch : all){
            if (branch.bestBranchDistanceSum < min){
                min = branch.bestBranchDistanceSum;
                bestBranch = branch;
            }
        }
        // return the bestBranch
        return bestBranch;
        //return all.get(RANDOM.nextInt(all.size()));
    }

    /**
     * Method that is used for catching the output from standard out. You should
     * write your own logic here.
     *
     * @param out the string that has been written in the standard out.
     */
    static final String ERROR_PREFIX = "ERROR_CODE_";

    static void output(String out) {
        System.out.println("--> " + out);
        // System.out.println("ERROR_CODE_" + i);
        if (out.startsWith(ERROR_PREFIX)) {
            final String err = out.substring(ERROR_PREFIX.length());
            System.out.println("Error code " + err);
            if (!FOUND_ERROR_MAP.containsKey(err))
                FOUND_ERROR_MAP.put(err, currentSample);
        }
    }

    private static class Branch {

        private InputSample bestSample;

        private Double bestBranchDistanceSum;

        public void checkIfBest(InputSample currentSample, double branchDistanceSum) {
            if (this.bestSample == null || branchDistanceSum < this.bestBranchDistanceSum) {
                this.bestSample = currentSample;
                this.bestBranchDistanceSum = branchDistanceSum;
            }
        }
    }

    private static class InputSample {

        private final ArrayList<String> input;
        private int pointer = 0;
        private float DistanceSum = 0;

        public float getDistanceSum() {
            return DistanceSum;
        }

        public InputSample(ArrayList<String> input) {
            this.input = input;
        }

        public InputSample permutation(String[] symbols) {
            final double mutationProbability = (double) CONFIGS[currentConfiguration][2];
            final ArrayList<String> res = new ArrayList<>(this.input);
            res.remove("R");
            for (int i = 0; i < res.size(); i++) {
                if (RANDOM.nextDouble() < mutationProbability) {
                    final int[] actions = { 0, 1, 2 };
                    final int action = actions[RANDOM.nextInt(actions.length)];

//                    if (action == 0) // add
//                        res.add(RANDOM.nextInt(res.size()), symbols[RANDOM.nextInt(symbols.length)]);
                    if (action == 0) // add
                        res.add(symbols[RANDOM.nextInt(symbols.length)]);
                    else if (action == 1) // replace
                        res.set(RANDOM.nextInt(res.size()), symbols[RANDOM.nextInt(symbols.length)]);
                    else if (action == 2) // remove
                        res.remove(RANDOM.nextInt(res.size()));
                    else
                        throw new RuntimeException("Unknown action " + action);
                }
            }
            res.add("R");
            return new InputSample(res);
        }

        public boolean hasNext() {
            return this.pointer < this.input.size();
        }

        public String next() {
            return this.input.get(this.pointer++);
        }
    }

    /**
     * Generate a random trace from an array of symbols.
     *
     * @param symbols the symbols from which a trace should be generated from.
     * @return a random trace that is generated from the given symbols.
     */

    static InputSample generateRandomTrace(String[] symbols) {
        ArrayList<String> trace = new ArrayList<>();
        for (int i = 0; i < traceLength; i++) {
            // pick 10 random inputs from input symbols.
            trace.add(symbols[RANDOM.nextInt(symbols.length)]);
        }
        trace.add("R"); // Reset symbol that marks that we have arrived at the end of a trace.
        return new InputSample(trace);
    }
}