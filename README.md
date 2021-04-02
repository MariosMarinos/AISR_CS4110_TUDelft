# AISR_CS4110_TUDelft

## Fuzzing
In the Fuzzing lab we tried to implement our fuzzer using Hill Climber optimizer method in order to minimize the branch distance to cover as many branches as possible. Then, in the report we had to compare the branch coverage for both Random fuzzing vs Hill Climber and then use a SOTA tool called AFL to compare again with our implementation. The code can be found on FuzzingLab/fuzzing/FuzzingLab.java and the report in the directory FuzzingLab.

## Symbolic Execution
In the Symbolic Execution lab, we had to implement a symbolic fuzzer that creates the path constraints, feed them to a solver using the opposite branch and check whether the opposite branch can be satisfiable or not. Presenting the results and then again use a SOTA tool called KLEE to find out if the results we get are good enough. The code can be found on SymbolicExecutionLab/symbolic/SymbolicExecutionLab.java and the report again in SymbolicExecutionLab.

## Automated Patching
Finally, in the last lab we had to implement a genetic algorithm that can fix failing tests to passing tests. The main idea is to initialize a population, use a fitness function based on failing tests, select best individuals based on fitness score using Roulette Selection and then mutate based on fault localization metric called Tarantula score (an extensive description of the above method can be found on the respective report), crossovering and finally use this samples as the new generation. Again, we had to compare our results to SOTA tool called astor that can find automatically patches for a given problem. 

In the above README I've included a brief introduction of the algorithms used for this course CS4110, more details can be found respectively on each lab's report.
