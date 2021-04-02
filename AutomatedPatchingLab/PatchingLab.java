package nl.tudelft.instrumentation.patching;

import com.sun.org.apache.xalan.internal.xsltc.runtime.Operators;

import java.io.*;
import java.util.*;

public class PatchingLab {

	static FileWriter fileFitness;
	static PrintWriter logger;
	static {
		// build a file to write all important data to,
		// allows for building graphs etc later
		final File folder = new File("./run_outputs/");
		folder.mkdirs();
		try {
			// start the first line as time and Fitness values.
			fileFitness = new FileWriter(new File(folder, "Fitness_vs_time.csv"));
			fileFitness.append("Time");
			fileFitness.append(",");
			fileFitness.append("Fitness value");
			fileFitness.append("\n");

		} catch (IOException e) {
			e.printStackTrace();
		}
		try {
			logger = new PrintWriter(new File(folder, "datalog.txt"));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}

	static void writeToFile(double Fitness) {
		// write to the file
		try {
			// take the values in seconds.
			fileFitness.append(String.valueOf((float)(System.currentTimeMillis() - startTime) / 1000));
			fileFitness.append(",");
			fileFitness.append(String.valueOf(Fitness));
			fileFitness.append("\n");
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	// function to sort hashmap by values.
	public static HashMap<Integer, Float> sortByValue(HashMap<Integer, Float> hm) {
		// Create a list from elements of HashMap
		List<Map.Entry<Integer, Float>> list =
				new LinkedList<>(hm.entrySet());

		// Sort the list
		Collections.sort(list, Collections.reverseOrder(Map.Entry.comparingByValue()));

		// put data from sorted list to hashmap
		HashMap<Integer, Float> temp = new LinkedHashMap<>();
		for (Map.Entry<Integer, Float> aa : list) {
			temp.put(aa.getKey(), aa.getValue());
		}
		return temp;
	}

	private static class Population_Sample {
		// keep track for each Sample in population, the fitness score,
		// and the tarantula score.
		private double fitness_score;
		private HashMap<Integer, Float> Tarantula_score = new HashMap<>();
		private String[] replacements;

		public Population_Sample(double fitness_score, HashMap<Integer, Float> tarantula_score, String[] replacements) {
			this.fitness_score = fitness_score;
			this.Tarantula_score = tarantula_score;
			this.replacements = replacements;
		}

		@Override
		public String toString() {
			return "Population_Sample{" +
					"fitness_score=" + fitness_score +
					 '}';
		}
	}

	// operators.
	static Map<Integer, String> Different_Operators = new HashMap<Integer, String>() {{
		put(0, "==");
		put(1, "!=");
		put(2, "<");
		put(3, ">");
		put(4, "<=");
		put(5, ">=");
	}};
	// 2 HashMaps to keep track of how many op in failure and successful tests.
	static HashMap<Integer, Integer> OP_Failures = new HashMap<>();
	static HashMap<Integer, Integer> OP_Success = new HashMap<>();
	static HashMap<Integer, Float> Tarantula_score = new HashMap<>();
	static Random r = new Random();
	static boolean isFinished = false;
	static boolean isPassing;
	static double Fitness;
	static int count_failed = 0;
	static int count_passing = 0;
	static String[] current_Sample;
	static int nTests = OperatorTracker.tests.size();
	static long startTime = System.currentTimeMillis();
	// list to keep the (replacements) samples.
	static ArrayList<String[]> new_samples = new ArrayList<>();
	// list to keep the samples and apply roulette selection, crossover, etc.
	static ArrayList<Population_Sample> Used_Samples = new ArrayList<>();
	// complementary array.
	static ArrayList<Population_Sample> HelpArray = new ArrayList<>();
	// create a hash map list to pick the best samples only with highest probabilities.
	static HashMap<Integer, Float> best_probabilities = new HashMap<>();

	// WORKS
	// create a string array with the corresponding probabilities that sum up to 1.
	// e.g. if we have [0.2,0.3,0.5,0.8] translates to [0.11, 0.277, 0.5444, 1]
	static double[] CreateProbabilities(){
		double[] Probabilities = new double[Used_Samples.size()];
		int i = 0;
		double sum_of_probabilities = 0;
		// calculate sum of the fitness values.
		double sum_fit = Used_Samples.stream()
				.map(item -> item.fitness_score)
				.reduce(0.0, (a, b) -> a + b);

		for (Population_Sample p_s : Used_Samples) {
			// calculate the individual score of each Sample.
			double individual_score = p_s.fitness_score / sum_fit;
			// add the previous probabilities also so e.g. first one will have 0.3 the next will have 0.3 + 0.2 (his own) so it sums up to 1.
			// and we have range of probabilities
			double Roulette_score = sum_of_probabilities + (individual_score);
			Probabilities[i] = Roulette_score;
			sum_of_probabilities += individual_score;
			best_probabilities.put(i, (float)p_s.fitness_score);
			i++;
		}
		return Probabilities;
	}

	// https://stackoverflow.com/questions/177271/roulette-selection-in-genetic-algorithms
	// WORKS.
	static void Roulette_Selection() {
		// method to scale the probabilities based on fitness value.
		double[] Probabilities = CreateProbabilities();

		best_probabilities = sortByValue(best_probabilities);

//		add first the top n BEST_SAMPLES first and then add the rest.
//		 get the indexes of the best samples.
		Object[] keys = best_probabilities.keySet().toArray();

		for (Object key : keys){
			Integer best_index = (Integer) key;
			new_samples.add(Used_Samples.get(best_index).replacements);
			HelpArray.add(Used_Samples.get(best_index));
			if (new_samples.size() == BEST_SAMPLES)
				break;
		}

		while (new_samples.size() < POPULATION){
			double rand = r.nextDouble();
			int i = 0;
			while (i < Probabilities.length){
				if (rand <= Probabilities[i]) break;
				else i++;
			}
			// in the new samples add the new replacements (chosen one)
			// and in HelpArray add the Finished samples, in same order as the replacements
			// to use later to get Tarantula scores.
			new_samples.add(Used_Samples.get(i).replacements);
			HelpArray.add(Used_Samples.get(i));
		}
		// mutate the best samples, and for the rest (that have been generated from roulette) apply crossover.
		for (int i = 0; i < BEST_SAMPLES; i ++){
			mutation(HelpArray.get(i).Tarantula_score, i);
		}
		//apply crossover to the rest of the samples (not the best mutated.)
		crossover(WHICH_CROSSOVER);
	}

	static void PickBest(){
		double[] Probabilities = CreateProbabilities();
		// sort to get the N best samples to next generation.
		best_probabilities = sortByValue(best_probabilities);
//		add first the top n BEST_SAMPLES first and then add the rest.
//		 get the indexes of the best samples.
		Object[] keys = best_probabilities.keySet().toArray();

		for (Object key : keys){
			Integer best_index = (Integer) key;
			new_samples.add(Used_Samples.get(best_index).replacements);
			HelpArray.add(Used_Samples.get(best_index));
			if (new_samples.size() == BEST_SAMPLES)
				break;
		}
		// mutate the first (BEST_SAMPLES) best samples that we pass to the next generation instantly.
		for (int i = 0; i < new_samples.size(); i ++){
			mutation(HelpArray.get(i).Tarantula_score, i);
		}


		// the rest POPULATION - BEST_SAMPLES will be cross-overed, where they also going to be
		// the best samples that we will crossover to keep track of the good Samples.
		for (Object key : keys){
			Integer best_index = (Integer) key;
			new_samples.add(Used_Samples.get(best_index).replacements);
			// need only for crossover, that's why we add it here and not in the first for loop!
			if (new_samples.size() == POPULATION)
				break;
		}

//		apply crossover to the best samples only!
		crossover(WHICH_CROSSOVER);
	}


	// crossover to the existing new_samples array String[].
	static void crossover(boolean WhichCrossover){
		int i = BEST_SAMPLES;
		while( i < new_samples.size()){
			// applying crossover directly to the arrays, so new_samples will be cross-overed directly.
			// apply 2-point crossover if true.
			if (WhichCrossover) {
				Two_Point_Crossover(new_samples.get(i), new_samples.get(i + 1), i);
			} else {
				One_Point_Crossover(new_samples.get(i), new_samples.get(i + 1), i);
			}
			i+= 2;
		}
	}
	// get the 2 String [] arrays to swap in the crossover (swap also the tarantula scores)
	// and the index of which sample it is.
	static void One_Point_Crossover(String[] a, String[] b, int index){
		// set the tarantula scores from key 1 to 353 key to crossover it.
		// find where to crossover (one-point crossover).
		int crossover = r.nextInt(a.length);
		for (int i = crossover; i < a.length; i++) {
			// swap the 2 numbers
			String tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
		}
		// set the cross-overed arrays as the new ones.
		new_samples.set(index, a);
		new_samples.set(index+1, b);
	}

	static void Two_Point_Crossover(String[] a, String[] b, int index){
		// find where to crossover (two-point crossover).
		int crossover_start = r.nextInt(a.length);
		// e.g. if c_s = 3 and length = 10, we get a 4 for sure (c_s + 1) and a random number in range (0-6)
		int crossover_finish = r.nextInt(a.length - crossover_start) + crossover_start + 1;
		for (int i = crossover_start; i < crossover_finish; i++) {
			// swap the 2 numbers
			String tmp = a[i];
			a[i] = b[i];
			b[i] = tmp;
			// swap the corresponding tarantula scores.
		}
		// set the cross-overed arrays as the new ones.
		new_samples.set(index, a);
		new_samples.set(index+1, b);
	}




	static void mutation (HashMap<Integer, Float> Tarantula, int index){
		// mutate randomly in the new_samples.get(index).
		// set a random mutation probability and tarantula threshold.
		String [] Sample = Arrays.copyOf(new_samples.get(index), new_samples.get(index).length);
		int j = 0 ;
		float[] Best_Mutates = new float[best_tarantula];
		int[] Best_Indexes = new int[best_tarantula];
		for (Map.Entry<Integer, Float> entry : Tarantula.entrySet()){
			if (j>=best_tarantula) {
				break;
			}
			Best_Mutates[j] = entry.getValue();
			Best_Indexes[j] = entry.getKey();
			j++;
			// pick from the top n highest tarantula.
		}

		// mutate MUTATE_NUM = 2 instead of 1 operations per sample picked among best tarantula operators.
		ArrayList<Integer> operations_picked = roulette(Best_Mutates);

		// for the two operators mutate randomly.
		for (int selected_index : operations_picked){
			String temp = mutate(Sample[Best_Indexes[selected_index]]);
			Sample[Best_Indexes[selected_index]] = temp;
		}

		// set the new curr_sample (after mutating) to old one.
		new_samples.set(index, Sample);
	}

	// WORKS (MIGHT NEED CHANGE? )
	static String mutate(String curr) {
		// pick a rand_num from 0 to 5 for a random operator.
		int ran = r.nextInt(6);
		// if it's the same keep trying different operators.
		while (Different_Operators.get(ran).equals(curr))
			ran = r.nextInt(6);
		return Different_Operators.get(ran);
	}

	// WORKS
	static ArrayList<Integer> roulette(float[] nums){
		float [] Prob = new float [nums.length];
		int j , i = 0;
		float sum_of_probabilities = 0;
		// calculate sum of the tarantula_scores.
		float sum_tarantula = 0;
		for ( j = 0; j < nums.length; j++){
			sum_tarantula += nums[j];
		}

		// calculate for each number the probability that it can happen.
		for ( j = 0 ; j < nums.length; j ++){
			float ind_sc = nums[j] / sum_tarantula;
			Prob[j] = sum_of_probabilities + ind_sc;
			sum_of_probabilities+=ind_sc;
		}

		ArrayList<Integer> changes = new ArrayList<>();

		while (changes.size() < MUTATE_OPERATORS) {
//			System.out.println("WHATS WRONG AGAIN....");
			double rand = r.nextDouble();
			// when i becomes Prob.length - 1
			for (i = 0; i < Prob.length; i++){
				if (rand <= Prob[i]){
					// if we have the same operator scheduled to change, don't add it again.
					if (!changes.contains(i)) changes.add(i);
					break;
				}
			}
		}
		return changes;
	}


	// initialize the population based on OperatorTracker.operators
	// WORKS
	static void initialize(HashMap<Integer, Float> Tarantula) {
		for (int i = 0; i < POPULATION; i++) {
			// create an empty array to fill the new values in.
			String [] Sample = Arrays.copyOf(current_Sample, current_Sample.length);
			int j = 0 ;
			float[] Best_Mutates = new float[best_tarantula];
			int[] Best_Indexes = new int[best_tarantula];
			for (Map.Entry<Integer, Float> entry : Tarantula.entrySet()){
				if (j>=best_tarantula) break;
				// get the best N samples and put them to two different arrays to use it in Roulette.
				Best_Mutates[j] = entry.getValue();
				Best_Indexes[j] = entry.getKey();
				j++;
			}
			// mutate MUTATE_NUM = 2 instead of 1 operations per sample picked among best tarantula operators.
			ArrayList<Integer> operations_picked = roulette(Best_Mutates);
			// for the two operators mutate randomly.
			for (int selected_index : operations_picked){
				String temp = mutate(Sample[Best_Indexes[selected_index]]);
//				System.out.println("was : " + Sample[Best_Indexes[selected_index]] + " and been changed to : "+ temp);
				Sample[Best_Indexes[selected_index]] = temp;
			}
			new_samples.add(Sample);
//			System.out.println("was : " + Sample[Best_Indexes[best]] + " and been changed to : "+ temp);
		}
	}

	// WORKS
	static void CalcTarantula() {
		for (int operation_nr = 0; operation_nr < OperatorTracker.operators.length; operation_nr++) {
			int Passed = 0, Failed = 0;
			float Tarantula = 0;
			// if operation_nr is on the hashmaps, then add get the value and use it to calculate tarantula score.
			if (OP_Success.containsKey(operation_nr)) Passed = OP_Success.get(operation_nr);
			if (OP_Failures.containsKey(operation_nr)) Failed = OP_Failures.get(operation_nr);

			float Failed_Metric = ((float) Failed) / count_failed;
			float Passed_Metric = ((float) Passed) / count_passing;
			Tarantula = Failed_Metric / (Failed_Metric + Passed_Metric);
			// for the operators that doesn't have any tests covering them
			// set Tarantula to 0.
			if (Double.isNaN(Tarantula)) Tarantula = 0;
			Tarantula_score.put(operation_nr, Tarantula);
		}
	}

	// WORKS
	// encounteredOperator gets called for each operator encountered while running tests
	static boolean encounteredOperator(String operator, int left, int right, int operator_nr) {
		String which_operator = whichTest + "_" + String.valueOf(operator_nr);

		if (combined.contains(which_operator)) {
			String replacement = current_Sample[operator_nr];
			if (replacement.equals("!=")) return left != right;
			if (replacement.equals("==")) return left == right;
			if (replacement.equals("<")) return left < right;
			if (replacement.equals(">")) return left > right;
			if (replacement.equals("<=")) return left <= right;
			if (replacement.equals(">=")) return left >= right;
			return false;
		}

		combined.add(which_operator);

		if (!temp_Map.containsKey(operator_nr)) temp_Map.put(operator_nr, 1);
		else temp_Map.put(operator_nr, temp_Map.get(operator_nr) + 1);

		String replacement = current_Sample[operator_nr];

		if (replacement.equals("!=")) return left != right;
		if (replacement.equals("==")) return left == right;
		if (replacement.equals("<")) return left < right;
		if (replacement.equals(">")) return left > right;
		if (replacement.equals("<=")) return left <= right;
		if (replacement.equals(">=")) return left >= right;
		return false;
	}

	// WORKS
	static boolean encounteredOperator(String operator, boolean left, boolean right, int operator_nr) {

		String which_operator = whichTest + "_" + String.valueOf(operator_nr);

		if (combined.contains(which_operator)) {
			String replacement = current_Sample[operator_nr];
			if (replacement.equals("!=")) return left != right;
			if (replacement.equals("==")) return left == right;
			return false;
		}

		combined.add(which_operator);

		if (!temp_Map.containsKey(operator_nr)) temp_Map.put(operator_nr, 1);
		else temp_Map.put(operator_nr, temp_Map.get(operator_nr) + 1);

		String replacement = current_Sample[operator_nr];

		if (replacement.equals("!=")) return left != right;
		if (replacement.equals("==")) return left == right;
		return false;
	}

	static int whichTest;
	static HashSet<String> combined =  new HashSet<>();
	static HashMap<Integer, Integer> temp_Map = new HashMap<>();

	// WORKS
	static void runTestAndCalcTarantula(){
		count_passing = 0;
		count_failed = 0;

		for (int i = 0; i < nTests; i++) {
			whichTest = i;

			boolean passed =OperatorTracker.runTest(i);
			// depending if the test passed or not assign it to the correct hashmap.
			if (passed) {
				count_passing++;
				// if the operator doesn't exist initialize it, otherwise add +1 to it.
				for (Map.Entry <Integer,Integer> entry : temp_Map.entrySet()){
					if (!OP_Success.containsKey(entry.getKey())) OP_Success.put(entry.getKey(), entry.getValue());
					else OP_Success.put(entry.getKey(), OP_Success.get(entry.getKey()) + entry.getValue());
				}
			}
			else {
				for (Map.Entry <Integer,Integer> entry : temp_Map.entrySet()){
					if (!OP_Failures.containsKey(entry.getKey()))
						OP_Failures.put(entry.getKey(), entry.getValue());
					else OP_Failures.put(entry.getKey(), OP_Failures.get(entry.getKey()) + entry.getValue());
				}
			}
			temp_Map.clear();
			combined.clear();
		}
		count_failed = nTests - count_passing;
		// calculate fitness of the replacements.
		Fitness = (double) count_passing / nTests;
		// calculate tarantula score.
		CalcTarantula();
		// add this sample to Population list.
		Used_Samples.add(new Population_Sample(Fitness, sortByValue(Tarantula_score), current_Sample));
		System.out.println(count_passing + "/" + nTests + " passed. Fitness: " + Fitness);

		// write to the file the best fit detected so far to get a smoother line.
		// if current fitness is better than the best, swap this to max.

		if (Fitness > Best_Fit_So_Far) Best_Fit_So_Far = Fitness;

		writeToFile(Best_Fit_So_Far);

		// clear the maps.
	}

	static double Best_Fit_So_Far = Integer.MIN_VALUE;
	// HYPER PARAMETERS OF GA.
	//final static int CROSSOVER_SAMPLES = 10;
	final static int POPULATION = 24;
	// if true apply 2-cross otherwise 1-cross.
	final static boolean WHICH_CROSSOVER = true;
	// best n-samples to get to the next generation without picking.
	final static int BEST_SAMPLES = 8;
	static int best_tarantula = OperatorTracker.operators.length;
	// 30mins runtime
	static int RUNTIME = 1800000;
	static int MUTATE_OPERATORS = 2;
	// if true Approach Roulette Selection otherwise PickBests.
	static boolean APPROACH_SELECT = false;


	static void run() {
		int point_cross = WHICH_CROSSOVER ? 2 : 1;
		// create the data log file with the configuration used.
		logger.println("Population :  " + POPULATION + "\n" +
				"Crossover : " + point_cross + "-point(s) crossover" + "\n"
				+ "Best Samples Passed to next generation with only mutating : " + BEST_SAMPLES + " \n" +
				"Best Tarantula to roulette and then mutate : " + best_tarantula + "\n" +
				"Mutate Operators : " + MUTATE_OPERATORS + "\n" +
				"RUNTIME : " + RUNTIME/1000 + " seconds");

		current_Sample = Arrays.copyOf(OperatorTracker.operators, OperatorTracker.operators.length);

		runTestAndCalcTarantula();
		// Generate POPULATION samples based on the first one.
		initialize(sortByValue(Tarantula_score));
		// Loop here, running your genetic algorithm until you think it is done.
		while (!isFinished) {
			OP_Failures.clear();
			OP_Success.clear();
			Tarantula_score.clear();
			// run with the new sample coming from generated population.
			current_Sample = new_samples.remove(0);
			runTestAndCalcTarantula();
//			 if we don't have any more samples, generate new population!!!
			if (new_samples.isEmpty()){
				// if for all samples in the population tarantula doesn't help to mutate
				System.out.println("Filling population...");
				if (APPROACH_SELECT) Roulette_Selection();
				else PickBest();
				System.out.println("Ending filling population...");
				// clear FinishedPopulation after have generated the new generation, HelpArray and the best probabilities.
				Used_Samples.clear();
				HelpArray.clear();
				best_probabilities.clear();
			}
			// if fitness > 90% stop or no new samples, or 8 minute has passed.
			if (System.currentTimeMillis() - startTime > RUNTIME || Fitness>=0.99) {
				System.out.println("Time finished, Exiting...");
				isFinished = true;
			}
		}

		try {
			fileFitness.flush();
			fileFitness.close();
			logger.flush();
			// close the program.
			System.exit(0);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	public static void output(String out) {
		// This will get called when the problem code tries to print things,
		// the prints in the original code have been removed for your convenience

		// System.out.println(out);
	}
}
