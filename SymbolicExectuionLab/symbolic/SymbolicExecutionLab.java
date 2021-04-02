package nl.tudelft.instrumentation.symbolic;

import java.io.*;
import java.util.*;
import com.microsoft.z3.*;
import nl.tudelft.instrumentation.fuzzing.FuzzingLab;
import java.util.Queue;
import java.util.Random;

/**
 * You should write your solution using this class.
 */


public class SymbolicExecutionLab {

    // Write the outputs in file to use them
    // to make graphs.
    static FileWriter fileErrors;
    static PrintWriter logger;

    static {
        // build a file to write all important data to,
        // allows for building graphs etc later
        final File folder = new File("./run_outputs/");
        folder.mkdirs();

        // find the first free problem id
        final File f = new File(folder, "datalog.txt");

        try {
            try {
                // start the first line as time and errors found.
                fileErrors = new FileWriter(new File(folder,"errors.csv"));
                fileErrors.append("Time");
                fileErrors.append(",");
                fileErrors.append("Unique Errors");
                fileErrors.append("\n");
            } catch (IOException e) {
                e.printStackTrace();
            }

            logger = new PrintWriter(new File(folder, "datalog.txt"));
        } catch (FileNotFoundException e) {
            e.printStackTrace();
            System.exit(0);
        }
    }


    static Random r = new Random();
    // map that represents the line number of the branch, and the condition found.
    public static final HashSet<String> FOUND_BRANCHES = new HashSet();
    private static final HashSet<String> FOUND_ERRORS = new HashSet();
    private final static ArrayList<String> SatisfiableInputs = new ArrayList<String>();
    private static long startTime = System.currentTimeMillis();
    private static int TraceLength = 100;
    private static String[] all_inputs;
    // 30 secs in milliseconds.
    static int RUNNING_TIME = 240000;


    static MyVar createVar(String name, Expr value, Sort s){
        Context c = PathTracker.ctx;
        // create var, assign value, add to path constraint
        // we show how to do it for creating new symbols
        // please add similar steps to the functions below in order to obtain a path constraint
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        PathTracker.z3model = c.mkAnd(c.mkEq(z3var, value), PathTracker.z3model);
        return new MyVar(z3var, name);
    }

    static MyVar createInput(String name, Expr value, Sort s){
        // create an input var, these should be free variables!
        Context c = PathTracker.ctx;
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        MyVar temp = new MyVar(z3var, name);
        PathTracker.inputs.add(temp);
        return temp;
    }

    static MyVar createBoolExpr(BoolExpr var, String operator){
        // any unary expression (!)
        if (operator.equals("!")){
            return new MyVar(PathTracker.ctx.mkNot(var));
        }
        else{
            error("Unable to create unary BoolExpr with " + var + ", operator : " + operator);
            // never reached but just Java.
            return new MyVar(PathTracker.ctx.mkFalse());

        }
    }

    static MyVar createBoolExpr(BoolExpr left_var, BoolExpr right_var, String operator){
        // any binary expression (&, &&, |, ||)
        if (operator.equals("&&") || operator.equals("&")){
            return new MyVar(PathTracker.ctx.mkAnd(left_var,right_var));
        }
        else if (operator.equals("||") || operator.equals("|")){
            return new MyVar(PathTracker.ctx.mkOr(left_var,right_var));
        }
        // XOR operation between 2 BoolExpr.
        else if (operator.equals("^")){
            return new MyVar(PathTracker.ctx.mkXor(left_var, right_var));
        }
        else{
            error("Not able to create BoolExpr with " + left_var + " and " + right_var + " operation " + operator);
            // never reached but just Java.
            return new MyVar(PathTracker.ctx.mkFalse());
        }
    }

    static MyVar createIntExpr(IntExpr var, String operator){
        // any unary expression (+, -)
        if(operator.equals("-")){
            return new MyVar(PathTracker.ctx.mkUnaryMinus(var));
        }
        else if (operator.equals("+")){
            return new MyVar(var);
        }
        else {
            error("Not able to create unary IntExpr with " + var + " operator : " + operator);
            // never reached but just Java.
            return new MyVar(PathTracker.ctx.mkFalse());
        }
    }

    static MyVar createIntExpr(IntExpr left_var, IntExpr right_var, String operator){
        // any binary expression (+, -, /, etc)
        if(operator.equals("+")){
            return new MyVar(PathTracker.ctx.mkAdd(left_var, right_var));
            }
        else if (operator.equals("-")){
            return new MyVar(PathTracker.ctx.mkSub(left_var, right_var));
        }
        else if (operator.equals("/")){
            return new MyVar(PathTracker.ctx.mkDiv(left_var, right_var));
        }
        else if (operator.equals("*")){
            return new MyVar(PathTracker.ctx.mkMul(left_var, right_var));
        }
        else if (operator.equals("%")){
            return new MyVar(PathTracker.ctx.mkMod(left_var, right_var));
        }
        else if (operator.equals("^")){
            return new MyVar(PathTracker.ctx.mkPower(left_var, right_var));
        }
        else if (operator.equals("==")){
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
        }
        else if (operator.equals("<=")){
            return new MyVar(PathTracker.ctx.mkLe(left_var, right_var));
        }
        else if (operator.equals(">=")){
            return new MyVar(PathTracker.ctx.mkGe(left_var, right_var));
        }
        else if(operator.equals(">")){
            return new MyVar(PathTracker.ctx.mkLt(left_var, right_var));
        }
        else if (operator.equals("<")){
            return new MyVar(PathTracker.ctx.mkGt(left_var, right_var));
        }
        else{
            error("Not able to create IntegerExpr with " + left_var + " and " + right_var + " operation " + operator);
            // never reached but just Java..
            return new MyVar(PathTracker.ctx.mkFalse());
        }
    }

    static MyVar createStringExpr(SeqExpr left_var, SeqExpr right_var, String operator){
        // we only support String.equals
        if (operator.equals("==")){
            return new MyVar(PathTracker.ctx.mkEq(left_var, right_var));
        }
        else
            error("Not able to create StringExpr with " + left_var + " and " + right_var + " operator : " + operator);
        // never reached but just Java.
        return new MyVar(PathTracker.ctx.mkFalse());
    }


    static void assign(MyVar var, String name, Expr value, Sort s){
        // all variable assignments, use single static assignment
        // name is var.name.
        // value is the actual value of the expression.
        // sort is the type of value.
        // check what type is the value and then assign it on a new MyVar.
        Context c = PathTracker.ctx;
        Expr z3var = c.mkConst(c.mkSymbol(name + "_" + PathTracker.z3counter++), s);
        var.z3var = z3var;
        PathTracker.z3model = c.mkAnd(c.mkEq(var.z3var, value), PathTracker.z3model);
    }


    // condition will be the z3 expression, the value that the expression has and the line_nr that it was found.
    static void encounteredNewBranch(MyVar condition, boolean value, int line_nr) {

        if (System.currentTimeMillis() >= startTime + RUNNING_TIME) {
            System.out.println("The running time(" + RUNNING_TIME / 1000 + "seconds) has exceed. Exiting...");
            System.out.println("Branches  are equal to : " + FOUND_BRANCHES.size());
            System.out.println("Errors founds are equal to : " + FOUND_ERRORS.size());

            // create the data log file with how many errors and branches it found.
            logger.println(" ERRORS " + FOUND_ERRORS.size() + " and "
                    + FOUND_BRANCHES.size() + " branch(es).");

            //close and flush the writers.
            try {
                fileErrors.flush();
                fileErrors.close();
                logger.flush();
            } catch (IOException e) {
                e.printStackTrace();
            }
            System.exit(0);
        }
        // write to the file
        try {
            // take the values in seconds.
            fileErrors.append(String.valueOf((System.currentTimeMillis() - startTime)));
            fileErrors.append(",");
            fileErrors.append(String.valueOf(FOUND_ERRORS.size()));
            fileErrors.append("\n");
        } catch (IOException e) {
            e.printStackTrace();
        }
        Context c = PathTracker.ctx;
        String concatenate = line_nr + "_" + value;
        // if the line_nr(branch) is not in FOUND_BRANCHES, add it.
        if (FOUND_BRANCHES.contains(concatenate)){
            return;
        }
        else {
            // if the fround doesn't exist add it.
            FOUND_BRANCHES.add(concatenate);
        }
        if (value) {
            // try to solve the not expression of condition var.
            PathTracker.solve(PathTracker.ctx.mkNot((BoolExpr) condition.z3var), false);
            // which true branches have been already encountered.
            PathTracker.z3branches = c.mkAnd(c.mkEq((condition.z3var), c.mkBool(true)), PathTracker.z3branches);
        }
        else {
            // try to solve the opposite condition (true) expression,
            // and send the true to check if that exists already, to not add .
            PathTracker.solve((BoolExpr)condition.z3var, false);
            // which false branches have been already encountered.
            PathTracker.z3branches = c.mkAnd(c.mkEq(c.mkNot((BoolExpr) condition.z3var), c.mkBool(true)), PathTracker.z3branches);
        }
    }

    static void newSatisfiableInput(LinkedList<String> new_inputs) {
        // hurray! found a new branch using these new inputs!
        // add the inputs to SatisfiableInputs Queue.
        for (String input : new_inputs){
            String inp = input.replaceAll("^\"|\"$", "");
            if (inp.equals(""))
                continue;
            SatisfiableInputs.add(inp);
        }
        // add 1 random symbol to make it explore a bit more.
        int i =0;
        for (;;i++){
            SatisfiableInputs.add(all_inputs[r.nextInt(all_inputs.length)]);
            if (i==5) break;
        }

        SatisfiableInputs.add("R");
        // when the trace ends, then we put the R symbol.
    }

    private static String current_input;
    private static ArrayList<String> RandomTrace;

    static String fuzz(String[] inputs){
        all_inputs = inputs;
        if (current_input==null)
            RandomTrace = generateRandomTrace(inputs);
        // if SatisfiableInputs is not empty we take the first element of the queue and the random trace has finished
        if (error_found){
            error_found = false;
            return "R";
        } // if SAT queue has no input create random trace, otherwise get the satisfiable inputs.
        else if (!SatisfiableInputs.isEmpty() && RandomTrace.isEmpty()){
            current_input = SatisfiableInputs.remove(0);
            if (current_input.equals("R")) {
                PathTracker.reset();
            }
            return current_input;
        }
        else {
//            System.out.println("RANDOM TRACE: " + RandomTrace);
            if (RandomTrace.isEmpty())
                RandomTrace=generateRandomTrace(inputs);
            current_input = RandomTrace.remove(0);
//            System.out.println("curr symbol : " + current_input);
            if (current_input.equals("R")) {
                PathTracker.reset();
            }
//            current_input = inputs[r.nextInt(inputs.length)];
            return current_input;
        }
    }

    static final String ERROR_PREFIX = "ERROR_CODE_";
    static boolean error_found = false;

    static void output(String out) {
        if (out.startsWith(ERROR_PREFIX)) {
            final String err = out.substring(ERROR_PREFIX.length());
//            System.out.println("Error code " + err);
            if (!FOUND_ERRORS.contains(err))
                FOUND_ERRORS.add(err);
            PathTracker.reset();
            error_found = true;
        }
    }

    static ArrayList<String> generateRandomTrace(String[] symbols) {
        ArrayList<String> trace = new ArrayList<>();
        for (int i = 0; i < TraceLength; i++) {
            // pick 10 random inputs from input symbols.
            trace.add(symbols[r.nextInt(symbols.length)]);
        }
        trace.add("R"); // Reset symbol that marks that we have arrived at the end of a trace.
        return trace;
    }

    // this is called for an error in our fuzzer, not for an error in the problems
    private static void error(String error) {
        System.out.println("[ERROR] " + error);
        throw new IllegalArgumentException(error);
    }
}