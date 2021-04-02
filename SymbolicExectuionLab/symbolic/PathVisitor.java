package nl.tudelft.instrumentation.symbolic;

import com.github.javaparser.*;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.StringLiteralExpr;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.type.*;

/**
 * This class is used to parse the RERS problem and instrument the problem file with our own object types
 * and method calls.
 *
 * @author Sicco Verwer
 */
public class PathVisitor extends ModifierVisitor<Object> {

    /** Used to give each variable an ID */
    int var_count = 1;

    /** Name of the source file to instrument */
    private String filename;
    private String pathFile = "nl.tudelft.instrumentation.symbolic.PathTracker";

    private String class_name = "";

    /**
     * Constructor
     * @param filename the name of the source file that we want to parse.
     */
    public PathVisitor(String filename) {
        this.filename = filename;
    }

    /** This method adds a new line in the source file under analysis to instrument the code
     * to do symbolic excecution.
     * @param node {@code Statement} to instrument
     * @param args additional arguments of JavaParser
     * @return {@code BlockStmt} that includes the {@code node} (statement in input) and the instrumented
     *         code for symbolic execution.
     */
    public Node addCode(Statement node, Statement new_statement, Object args){
        if (node.getParentNode().isPresent()){
        
            Node parent = node.getParentNode().get();

            if (parent instanceof BlockStmt) {
                // if {@code node} is within a BlockStmt (i.e., withing a block with
                // open-close curly brackets), we just add the new line for coverage tracking
                BlockStmt block = (BlockStmt) parent;
                int line = node.getBegin().get().line;
                int position = block.getStatements().indexOf(node);
                block.addStatement(position, new_statement);
            } else {
                // if {@code node} is not within a BlockStmt (e.g., true branch of an if condition
                // with no curly brackets), we need to create a BlockStmt first
                BlockStmt block = new BlockStmt();
                block.addStatement(new_statement);
                block.addStatement(node);
                return block;
            }
        }
        return node;
    }

    /**
     * This method is used to insert a statement after a given statement. Used to insert additional statement
     * in the main method (right after "String input = stdin.readLine();"
     * @param node the node that represents the statement for which we want to add a statement after.
     * @param new_statement the new statement that needs to be inserted
     * @param args additional arguments that were given to the JavaParser
     * @return a node containing our instrumented code.
     */
    public Node addCodeAfter(Statement node, Statement new_statement, Object args){
        if (node.getParentNode().isPresent()){
        
            Node parent = node.getParentNode().get();

            if (parent instanceof BlockStmt) {
                // if {@code node} is within a BlockStmt (i.e., withing a block with
                // open-close curly brackets), we just add the new line for coverage tracking
                BlockStmt block = (BlockStmt) parent;
                int line = node.getBegin().get().line;
                int position = block.getStatements().indexOf(node) + 1;
                block.addStatement(position, new_statement);
            } else {
                // if {@code node} is not within a BlockStmt (e.g., true branch of an if condition
                // with no curly brackets), we need to create a BlockStmt first
                BlockStmt block = new BlockStmt();
                block.addStatement(node);
                block.addStatement(new_statement);
                return block;
            }
        }
        return node;
    }

    /**
     * Method that is used to convert each expression into the corresponding Z3 expression.
     * @param node the expression.
     * @param args additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    public Expression addOwnExpressionCode(Expression node, Object args) {
        while(node instanceof EnclosedExpr) node = ((EnclosedExpr)node).getInner();

        // Prepend "my_" to the name of the variable.
        if(node instanceof NameExpr){
            return new NameExpr("my_" + node.toString());
        } else if(node instanceof LiteralExpr){ // convert each variable (that is a literal) to a MyVar object.
            NodeList<Expression> node_list = new NodeList<Expression>();
            node_list.add(node.clone());
            return new MethodCallExpr(new NameExpr(pathFile),"tempVar", node_list);
        } else if(node instanceof BinaryExpr){ // convert binary expressions to the corresponding Z3 binary expressions.
            BinaryExpr bine = (BinaryExpr) node;
            Expression left = addOwnExpressionCode(bine.getLeft(), args);
            Expression right = addOwnExpressionCode(bine.getRight(), args);
            NodeList<Expression> node_list = new NodeList<Expression>();
            node_list.add(left);
            node_list.add(right);
            node_list.add(new StringLiteralExpr(bine.getOperator().asString()));
            return new MethodCallExpr(new NameExpr(pathFile),"binaryExpr",node_list);
        } else if(node instanceof MethodCallExpr){ // convert "equals" calls to the MyVar equals calls
            MethodCallExpr mete = (MethodCallExpr) node;
            Expression scope = addOwnExpressionCode(mete.getScope().get(), args);
            NodeList<Expression> arguments = new NodeList<Expression>();
            for(int i = 0; i < mete.getArguments().size(); ++i){
                arguments.add(addOwnExpressionCode(mete.getArguments().get(i), args));
            }
            if(mete.getName().asString().equals("equals")){
                arguments.add(scope);
                return new MethodCallExpr(new NameExpr(pathFile),"equals",arguments);
            } else {
                return new MethodCallExpr(scope, mete.getName().asString(), arguments);
            }
        } else if(node instanceof ArrayAccessExpr){ // convert array access expression to the corresponding Z3 array access expression
            ArrayAccessExpr aae = (ArrayAccessExpr) node;
            Expression name = addOwnExpressionCode(aae.getName(), args);
            Expression index = addOwnExpressionCode(aae.getIndex(),args);
            NodeList<Expression> node_list = new NodeList<Expression>();
            node_list.add(name);
            node_list.add(index);
            return new MethodCallExpr(new NameExpr(pathFile),"arrayInd", node_list);
        } else if(node instanceof UnaryExpr){ // convert unary expression to the corresponding Z3 unary expression
            UnaryExpr ue = (UnaryExpr) node;
            Expression expr = addOwnExpressionCode(ue.getExpression(),args);
            if(ue.getOperator().asString().equals("++") || ue.getOperator().asString().equals("--")){
                NodeList<Expression> node_list = new NodeList<Expression>();
                node_list.add(expr);
                node_list.add(new StringLiteralExpr(ue.getOperator().asString()));
                node_list.add(new BooleanLiteralExpr(ue.isPrefix()));
                return new MethodCallExpr(new NameExpr(pathFile),"increment", node_list);
            }
            else if(ue.getOperator().asString().equals("+") || ue.getOperator().asString().equals("-")){
                NodeList<Expression> node_list = new NodeList<Expression>();
                node_list.add(expr);
                node_list.add(new StringLiteralExpr(ue.getOperator().asString()));
                return new MethodCallExpr(new NameExpr(pathFile),"unaryExpr", node_list);
            }
            else if(ue.getOperator().asString().equals("!")){
                NodeList<Expression> node_list = new NodeList<Expression>();
                node_list.add(expr);
                node_list.add(new StringLiteralExpr(ue.getOperator().asString()));
                return new MethodCallExpr(new NameExpr(pathFile),"unaryExpr", node_list);
            }
        } else if(node instanceof ConditionalExpr){ // convert conditional expression to the corresponding Z3 conditional expression
            ConditionalExpr ce = (ConditionalExpr) node;
            NodeList<Expression> node_list = new NodeList<Expression>();
            node_list.add(addOwnExpressionCode(ce.getCondition(),args));
            node_list.add(addOwnExpressionCode(ce.getThenExpr(),args));
            node_list.add(addOwnExpressionCode(ce.getElseExpr(),args));
            return new MethodCallExpr(new NameExpr(pathFile),"conditional", node_list);
        }
        return node.clone();
    }

    /**
     * Method that is used to convert an if-statement to a "myIf" method call.
     * Actually the call is added just right above the if-statement.
     * @param n the node that represents an if-statement.
     * @param args additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    public ExpressionStmt createMyIf(IfStmt n, Object args){
        Expression node = this.addOwnExpressionCode(n.getCondition(), args);
        Expression n_orig = n.getCondition().clone();
        NodeList<Expression> node_list = new NodeList<Expression>();
        node_list.add(node);
        node_list.add(n_orig);
        node_list.add(new IntegerLiteralExpr(n.getBegin().get().line));
        MethodCallExpr myif = new MethodCallExpr(new NameExpr(pathFile),"myIf",node_list);
        return new ExpressionStmt(myif);
    }

    /**
     * Method that is used to convert assigment operations to "myAssign" method calls.
     * @param node the node that represents an assignment expression.
     * @param args additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    public ExpressionStmt createMyAssign(AssignExpr node, Object args){
        NodeList<Expression> node_list = new NodeList<Expression>();
        if(node.getTarget() instanceof ArrayAccessExpr){
            ArrayAccessExpr aae = (ArrayAccessExpr)node.getTarget();
            node_list.add(this.addOwnExpressionCode(aae.getName(),args));
            node_list.add(this.addOwnExpressionCode(aae.getIndex(),args));
        } else {
            node_list.add(this.addOwnExpressionCode(node.getTarget(),args));
        }
        node_list.add(this.addOwnExpressionCode(node.getValue(),args));
        node_list.add(new StringLiteralExpr(node.getOperator().asString()));
        MethodCallExpr myassign = new MethodCallExpr(new NameExpr(pathFile),"myAssign", node_list);
        return new ExpressionStmt(myassign);
    }

    /**
     * Method that is used to create the MyVar variables for each field that is listed in the source file.
     * @param node the node that represents a declaration of a variable.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    public VariableDeclarator createMyField(VariableDeclarator node, Object arg){
        JavaParser jp = new JavaParser();
        // Prepend "my_" to the name of the variable.
        node.setName(new SimpleName("my_" + node.getName().toString()));
        // Check whether we are deadline with a variable that is used to store an array.
        if(node.getType().getArrayLevel() != 0){
            node.setType(new ClassOrInterfaceType("MyVar[]"));
            if(node.getInitializer().isPresent()){
                if(node.getInitializer().get() instanceof ArrayInitializerExpr){
                    ArrayInitializerExpr aie = (ArrayInitializerExpr)node.getInitializer().get();
                    int i = 0;
                    // Convert each element in the array into a MyVar object
                    for(Expression e : aie.getValues()){
                        NodeList<Expression> node_list = new NodeList<Expression>();
                        node_list.add(e.clone());
                        node_list.add(new StringLiteralExpr(node.getName().asString() + String.valueOf(i)));
                        e.replace(new MethodCallExpr(new NameExpr(pathFile), "myVar", node_list));
                        i++;
                    }
                } else {
                    NodeList<Expression> node_list = new NodeList<Expression>();
                    node_list.add(addOwnExpressionCode(node.getInitializer().get(), arg));
                    node_list.add(new StringLiteralExpr(node.getName().asString()));
                    node.setInitializer(new MethodCallExpr(new NameExpr(pathFile), "myVar", node_list));
                }
            }
        } else {
            // Convert booleans, integers and strings to MyVar objects.
            if(node.getType().asString().equals("boolean") || node.getType().asString().equals("int") || node.getType().asString().equals("String")){
                node.setType(new ClassOrInterfaceType("MyVar"));
                if(node.getInitializer().isPresent()){
                    NodeList<Expression> node_list = new NodeList<Expression>();
                    node_list.add(node.getInitializer().get());
                    node_list.add(new StringLiteralExpr(node.getName().asString()));
                    node.setInitializer(new MethodCallExpr(new NameExpr(pathFile), "myVar", node_list));
                }
            }
        }
        return node;
    }

    /**
     * Method that specifies what should be done when we have encountered a field declaration
     * in the AST.
     * @param node the node that represents the field declaration.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    @Override
    public Node visit(FieldDeclaration node, Object arg){
        if(node.getParentNode().isPresent()){
            for(VariableDeclarator vard : node.getVariables()){
                // For each field that is listed in the source file, create a copy of the field and give it the
                // MyVar type so that we can use these fields in the symbolic execution.
                FieldDeclaration fd = new FieldDeclaration(node.getModifiers(), createMyField(vard.clone(), arg));
                ClassOrInterfaceDeclaration decl = (ClassOrInterfaceDeclaration) node.getParentNode().get();
                decl.getMembers().add(fd);
            }
        }
        return node;
    }

    /**
     * Method that specifies what should be done when we have encountered a method declaration
     * in the AST.
     * @param node the node that represents the Method Declaration.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    @Override
    public Node visit(MethodDeclaration node, Object arg){
        if(node.getName().toString().contains("calculate")){
            for(Parameter par : node.clone().getParameters()){
                // For each parameter of the method, create a copy of the parameter and give it the MyVar type
                // This makes sure that we can also use the parameters in the symbolic execution.
                node.addParameter("MyVar", "my_" + par.getName().asString());
            }
        }
        return (Node) super.visit(node, arg);
    }

    /**
     * Method that specifies what should be done when we have encountered a class or interface
     * declaration in the AST.
     * @param node the node that represents a class or interface declaration.
     * @param arg the additional arguments that were given to the JavaParser.
     * @return a node containing the instrumented code.
     */
    @Override
    public Node visit(ClassOrInterfaceDeclaration node, Object arg){
        this.class_name = node.getName().toString();
        return (Node) super.visit(node, arg);
    }

    /**
     * Method that specifies what should be done when we have encountered an expression statement
     * in the AST.
     * @param node the node that represents the expression statement.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    @Override
    public Node visit(ExpressionStmt node, Object arg) {
        // What should be done when it is a variable declaration.
        if(node.getExpression() instanceof VariableDeclarationExpr){
            //System.out.println(node.toString());
            if(node.toString().contains("String input = stdin")){
                Statement staticStatement = StaticJavaParser.parseStatement("if(input.equals(\"R\")){ eca = new " + class_name + "(); continue; }");
                this.addCodeAfter(node, staticStatement, arg);
                staticStatement = StaticJavaParser.parseStatement("MyVar my_input = " + pathFile + ".myInputVar(input, \"input\");");
                this.addCodeAfter(node, staticStatement, arg);
                staticStatement = StaticJavaParser.parseStatement("String input = " + pathFile + ".fuzz(eca.inputs);");
                node.replace(staticStatement);
            }
        }

        // What should be done when it is an assign expression.
        if(node.getExpression() instanceof AssignExpr){
            // Convert it to the corresponding Z3 expression.
            ExpressionStmt myassign = this.createMyAssign((AssignExpr)node.getExpression().clone(), arg);
            this.addCode(node, myassign, arg);
        }

        // What should be done when it is a method call expresion.
        if(node.getExpression() instanceof MethodCallExpr){
            MethodCallExpr n = ((MethodCallExpr)node.getExpression()).clone();
            if(n.getName().asString().startsWith("calculate")){
                for(Expression expr : n.getArguments()){
                    // We basically add an extra argument to a method if its name starts with "calculate"
                    ((MethodCallExpr)node.getExpression()).addArgument(addOwnExpressionCode(expr, arg));
                }
            }
        }

        // Catch the out from in the standard out.
        if (node.getExpression() instanceof MethodCallExpr) {
            MethodCallExpr mce = (MethodCallExpr)node.getExpression();
            if (node.toString().contains("System.out")) {
                this.addCode(node, new ExpressionStmt(new MethodCallExpr(new NameExpr(pathFile),"output",mce.getArguments())), arg);
            }
        }
        return node;
    }

    /**
     * Method that specifies what should we done when we have encountered
     * an if-statement in the AST.
     * @param node the node that represents the if-statement.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    @Override
    public Node visit(IfStmt node, Object arg) {
        ExpressionStmt myif = this.createMyIf(node.clone(), arg);
        this.addCode(node, myif, arg);
        return (Node) super.visit(node, arg);
    }

    /**
     * Method to add import statements in the top of the source file.
     * @param node the node that defines the root of the source file.
     * @param arg additional arguments that were given to the JavaParser.
     * @return a node that contains our instrumented code.
     */
    @Override
    public Node visit(CompilationUnit node, Object arg) {
        node.addImport("nl.tudelft.instrumentation.symbolic.*");
        return (Node) super.visit(node, arg);
    }
}
