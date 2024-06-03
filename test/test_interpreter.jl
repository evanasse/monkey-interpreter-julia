using Test

include("../src/interpreter.jl")

### LEXER_
@testset "lexer: next token" begin
    struct ExpectedResult
        type::Type{<:TokenType}
        literal::String

        function ExpectedResult(type::Type{<:TokenType}, literal::String)
            return new(type, literal)
        end

    end

    input = """
    let five = 5;
    let ten = 10;
    let add = fn(x, y) {
        x + y;
    };
    let result = add(five, ten);
    !-/*5;
    5 < 10 > 5;

    if (5 < 10) {
        return true;
    } else {
        return false;
    }

    10 == 10;
    10 != 9;
    "foobar"
    "foo bar"
    [1, 2];
    {\"foo\": \"bar\"}
    """

    expected_results = [
        ExpectedResult(LET, "let"),
        ExpectedResult(IDENT, "five"),
        ExpectedResult(ASSIGN, "="),
        ExpectedResult(INT, "5"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(LET, "let"),
        ExpectedResult(IDENT, "ten"),
        ExpectedResult(ASSIGN, "="),
        ExpectedResult(INT, "10"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(LET, "let"),
        ExpectedResult(IDENT, "add"),
        ExpectedResult(ASSIGN, "="),
        ExpectedResult(FUNCTION, "fn"),
        ExpectedResult(LPAREN, "("),
        ExpectedResult(IDENT, "x"),
        ExpectedResult(COMMA, ","),
        ExpectedResult(IDENT, "y"),
        ExpectedResult(RPAREN, ")"),
        ExpectedResult(LBRACE, "{"),
        ExpectedResult(IDENT, "x"),
        ExpectedResult(PLUS, "+"),
        ExpectedResult(IDENT, "y"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(RBRACE, "}"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(LET, "let"),
        ExpectedResult(IDENT, "result"),
        ExpectedResult(ASSIGN, "="),
        ExpectedResult(IDENT, "add"),
        ExpectedResult(LPAREN, "("),
        ExpectedResult(IDENT, "five"),
        ExpectedResult(COMMA, ","),
        ExpectedResult(IDENT, "ten"),
        ExpectedResult(RPAREN, ")"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(BANG, "!"),
        ExpectedResult(MINUS, "-"),
        ExpectedResult(SLASH, "/"),
        ExpectedResult(ASTERISK, "*"),
        ExpectedResult(INT, "5"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(INT, "5"),
        ExpectedResult(LT, "<"),
        ExpectedResult(INT, "10"),
        ExpectedResult(GT, ">"),
        ExpectedResult(INT, "5"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(IF, "if"),
        ExpectedResult(LPAREN, "("),
        ExpectedResult(INT, "5"),
        ExpectedResult(LT, "<"),
        ExpectedResult(INT, "10"),
        ExpectedResult(RPAREN, ")"),
        ExpectedResult(LBRACE, "{"),
        ExpectedResult(RETURN, "return"),
        ExpectedResult(TRUE, "true"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(RBRACE, "}"),
        ExpectedResult(ELSE, "else"),
        ExpectedResult(LBRACE, "{"),
        ExpectedResult(RETURN, "return"),
        ExpectedResult(FALSE, "false"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(RBRACE, "}"),
        ExpectedResult(INT, "10"),
        ExpectedResult(EQ, "=="),
        ExpectedResult(INT, "10"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(INT, "10"),
        ExpectedResult(NOT_EQ, "!="),
        ExpectedResult(INT, "9"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(STR, "foobar"),
        ExpectedResult(STR, "foo bar"),
        ExpectedResult(LBRACKET, "["),
        ExpectedResult(INT, "1"),
        ExpectedResult(COMMA, ","),
        ExpectedResult(INT, "2"),
        ExpectedResult(RBRACKET, "]"),
        ExpectedResult(SEMICOLON, ";"),
        ExpectedResult(LBRACE, "{"),
        ExpectedResult(STR, "foo"),
        ExpectedResult(COLON, ":"),
        ExpectedResult(STR, "bar"),
        ExpectedResult(RBRACE, "}"),
        ExpectedResult(EOF, string(Char(0))),
    ]

    lexer = Lexer(input)

    for result in expected_results
        token = nexttoken!(lexer)

        @test token.type == result.type
        @test token.literal == result.literal
    end

end
### _LEXER

### PARSER_
function test_letstatement(statement::Statement, name::String)
    t = tokenliteral(statement)
    @assert t == "let" "token literal not 'let'. Got '$(t)'."

    t = typeof(statement)
    @assert t == LetStatement "statement not a LetStatement. Got '$(t)'"

    t = statement.name.value
    @assert t == name "let_statement name value not $(name). Got '$(t)'."

    t = tokenliteral(statement.name)
    @assert t == name "let_statement name token literal value not $(name). Got '$(t)'."

    return true
end

function check_parsererrors(parser::Parser)
    errors = parser.errors

    if length(errors) == 0
        return true
    end

    println("parser has $(length(errors)) error$(if length(errors) > 1; "s"; else; ""; end)")

    for error in errors
        println("parser error: $error")
    end

    false
end

function test_integerliteral(integer_literal::Expression, value::Int)
    @assert typeof(integer_literal) == IntegerLiteral
    @assert integer_literal.value == value
    @assert tokenliteral(integer_literal) == string(value)

    true
end

function test_identifier(identifier::Expression, value::String)
    @assert typeof(identifier) == Identifier
    @assert identifier.value == value
    @assert tokenliteral(identifier) == value

    true
end

function test_boolean(boolean::Expression, value::Bool)
    @assert typeof(boolean) == Boolean
    @assert boolean.value == value
    @assert tokenliteral(boolean) == string(value)

    true
end

function test_literalexpression(expression::Expression, expected::T) where {T}
    if typeof(expected) == Int
        return test_integerliteral(expression, expected)
    elseif typeof(expected) == String
        return test_identifier(expression, expected)
    elseif typeof(expected) == Bool
        return test_boolean(expression, expected)
    end
    println("type of 'expected' not handled. got $(typeof(expected))")

    false
end

function test_infixexpression(expression::Expression, left::T, operator::String, right::U) where {T,U}
    @assert typeof(expression) == InfixExpression
    @assert test_literalexpression(expression.left, left)
    @assert expression.operator == operator
    @assert test_literalexpression(expression.right, right)

    true
end

@testset "parser: return statements" begin
    struct ReturnStatementTest{T}
        input::String
        expected_value::T
    end

    tests = [
        ReturnStatementTest("return 5;", 5)
        ReturnStatementTest("return true;", true)
        ReturnStatementTest("return y;", "y")
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test length(program.statements) == 1

        statement = program.statements[1]

        @test typeof(statement) == ReturnStatement
        @test tokenliteral(statement) == "return"
        @test test_literalexpression(statement.return_value, test.expected_value)
    end
end

@testset "parser: let statements" begin
    struct LetStatementTest{T}
        input::String
        expected_identifier::String
        expected_value::T
    end

    tests = [
        LetStatementTest("let x = 5;", "x", 5),
        LetStatementTest("let y = true;", "y", true),
        LetStatementTest("let foobar = y;", "foobar", "y"),
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test length(program.statements) == 1

        statement = program.statements[1]
        @test typeof(statement) == LetStatement
        @test test_letstatement(statement, test.expected_identifier)

        value = statement.value
        @test test_literalexpression(value, test.expected_value)
    end
end

@testset "parser: identifier expression" begin
    input = "foobar;"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    identifier = statement.expression
    @test typeof(identifier) == Identifier

    @test test_literalexpression(identifier, "foobar")
end

@testset "parser: integer literal expression" begin
    input = "5;"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    literal = statement.expression
    @test typeof(literal) == IntegerLiteral

    @test test_literalexpression(literal, 5)
end

@testset "parser: boolean literal expression" begin
    input = """
    true;
    false;
    """

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 2

    expected_results = [
        true,
        false,
    ]

    for (i, expected_result) in enumerate(expected_results)
        statement = program.statements[i]
        @test typeof(statement) == ExpressionStatement

        boolean = statement.expression
        @test typeof(boolean) == Boolean

        @test test_literalexpression(boolean, expected_result)
    end
end

@testset "parser: string literal" begin
    input = "\"hello world\";"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)


    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    literal = statement.expression
    @test typeof(literal) == StringLiteral

    @test literal.value == "hello world"

end

@testset "parser: function literal" begin
    input = "fn(x, y) { x + y; }"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    func = statement.expression
    @test typeof(func) == FunctionLiteral

    @test length(func.parameters) == 2

    @test test_literalexpression(func.parameters[1], "x")
    @test test_literalexpression(func.parameters[2], "y")

    @test length(func.body.statements) == 1

    body_statement = func.body.statements[1]
    @test test_infixexpression(body_statement.expression, "x", "+", "y")
end

@testset "parser: function parameters" begin
    struct FunctionTest
        input::String
        parameters::Array{String}
    end

    tests = [
        FunctionTest("fn() {};", []),
        FunctionTest("fn(x) {};", ["x"]),
        FunctionTest("fn(x, y, z) {};", ["x", "y", "z"]),
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        statement = program.statements[1]
        func = statement.expression

        @test length(func.parameters) == length(test.parameters)

        for (i, identifier) in enumerate(test.parameters)
            @test test_literalexpression(func.parameters[i], identifier)
        end
    end
end

@testset "parser: call expression" begin
    input = "add(1, 2 * 3, 4 + 5);"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    call_expression = statement.expression
    @test typeof(call_expression) == CallExpression

    @test test_identifier(call_expression.func, "add")
    @test length(call_expression.arguments) == 3

    @test test_literalexpression(call_expression.arguments[1], 1)
    @test test_infixexpression(call_expression.arguments[2], 2, "*", 3)
    @test test_infixexpression(call_expression.arguments[3], 4, "+", 5)
end

@testset "parser: call expression arguments" begin
    struct CallExpressionArgumentsTest
        input::String
        amount_arguments::Int
    end

    tests = [
        CallExpressionArgumentsTest("add(1)", 1),
        CallExpressionArgumentsTest("add(1, b)", 2),
        CallExpressionArgumentsTest("add(1, b, fn(x,y){x+y})", 3),
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test length(program) == 1

        statement = program.statements[1]
        @test typeof(statement) == ExpressionStatement

        call_expression = statement.expression
        @test typeof(call_expression) == CallExpression

        @test length(call_expression.arguments) == test.amount_arguments
    end

end

@testset "parser: prefix expression" begin
    struct PrefixTest{T}
        input::String
        operator::String
        value::T
    end

    tests = [
        PrefixTest("!5;", "!", 5),
        PrefixTest("-15;", "-", 15),
        PrefixTest("!true", "!", true),
        PrefixTest("!false", "!", false),
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test length(program) == 1

        statement = program.statements[1]
        @test typeof(statement) == ExpressionStatement

        expression = statement.expression
        @test typeof(expression) == PrefixExpression

        @test expression.operator == test.operator
        @test test_literalexpression(expression.right, test.value)
    end
end

@testset "parser: infix expression" begin
    struct InfixTest{T}
        input::String
        left::T
        operator::String
        right::T
    end

    tests = [
        InfixTest("5 + 5;", 5, "+", 5),
        InfixTest("5 - 5;", 5, "-", 5),
        InfixTest("5 * 5;", 5, "*", 5),
        InfixTest("5 / 5;", 5, "/", 5),
        InfixTest("5 > 5;", 5, ">", 5),
        InfixTest("5 < 5;", 5, "<", 5),
        InfixTest("5 == 5;", 5, "==", 5),
        InfixTest("5 != 5;", 5, "!=", 5),
        InfixTest("true == true;", true, "==", true),
        InfixTest("true != false;", true, "!=", false),
        InfixTest("false == false;", false, "==", false),
    ]

    for test in tests

        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test length(program) == 1

        statement = program.statements[1]
        @test typeof(statement) == ExpressionStatement

        expression = statement.expression
        @test test_infixexpression(expression, test.left, test.operator, test.right)
    end

end


@testset "parser: if expression" begin
    input = "if (x < y) { x }"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    expression = statement.expression
    @test typeof(expression) == IfExpression

    @test test_infixexpression(expression.condition, "x", "<", "y")

    @test length(expression.consequence.statements) == 1

    consequence = expression.consequence.statements[1]
    @test !isnothing(consequence)

    @test test_identifier(consequence.expression, "x")

    @test isnothing(expression.alternative)
end

@testset "parser: if else expression" begin
    input = "if (x < y) { x } else { y }"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    expression = statement.expression
    @test typeof(expression) == IfExpression

    @test test_infixexpression(expression.condition, "x", "<", "y")

    @test length(expression.consequence.statements) == 1

    consequence = expression.consequence.statements[1]
    @test test_identifier(consequence.expression, "x")

    alternative = expression.alternative.statements[1]
    @test test_identifier(alternative.expression, "y")
end

@testset "parser: operator precedence" begin
    struct TestCase
        input::String
        expected::String
    end

    tests = [
        TestCase("-a * b", "((-a) * b)"),
        TestCase("!-a", "(!(-a))"),
        TestCase("a + b + c", "((a + b) + c)"),
        TestCase("a + b - c", "((a + b) - c)"),
        TestCase("a * b * c", "((a * b) * c)"),
        TestCase("a * b / c", "((a * b) / c)"),
        TestCase("a + b / c", "(a + (b / c))"),
        TestCase("a + b * c + d / e - f", "(((a + (b * c)) + (d / e)) - f)"),
        TestCase("3 + 4; -5 * 5", "(3 + 4)((-5) * 5)"),
        TestCase("5 > 4 == 3 < 4", "((5 > 4) == (3 < 4))"),
        TestCase("5 < 4 != 3 > 4", "((5 < 4) != (3 > 4))"),
        TestCase("3 + 4 * 5 == 3 * 1 + 4 * 5", "((3 + (4 * 5)) == ((3 * 1) + (4 * 5)))"),
        TestCase("true", "true"),
        TestCase("false", "false"),
        TestCase("3 > 5 == false", "((3 > 5) == false)"),
        TestCase("3 < 5 == true", "((3 < 5) == true)"),
        TestCase("1 + (2 + 3) + 4", "((1 + (2 + 3)) + 4)"),
        TestCase("(5 + 5) * 2", "((5 + 5) * 2)"),
        TestCase("2 / (5 + 5)", "(2 / (5 + 5))"),
        TestCase("-(5 + 5)", "(-(5 + 5))"),
        TestCase("!(true == true)", "(!(true == true))"),
        TestCase("a + add(b * c) + d", "((a + add((b * c))) + d)"),
        TestCase("add(a, b, 1, 2 * 3, 4 + 5, add(6, 7 * 8))", "add(a, b, 1, (2 * 3), (4 + 5), add(6, (7 * 8)))"),
        TestCase("add(a + b + c * d / f + g)", "add((((a + b) + ((c * d) / f)) + g))"),
        TestCase("a * [1, 2, 3, 4][b * c] * d", "((a * ([1, 2, 3, 4][(b * c)])) * d)"),
        TestCase("add(a * b[2], b[1], 2 * [1, 2][1])", "add((a * (b[2])), (b[1]), (2 * ([1, 2][1])))"),
    ]

    for test in tests
        lexer = Lexer(test.input)

        parser = Parser(lexer)

        program = parse_program!(parser)
        @assert check_parsererrors(parser)

        @test string(program) == test.expected
    end
end

@testset "parser: array literals" begin
    input = "[1, 2 * 2, 3 + 3]"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    array_literal = statement.expression
    @test typeof(array_literal) == ArrayLiteral

    @test length(array_literal.elements) == 3

    @test test_integerliteral(array_literal.elements[1], 1)
    @test test_infixexpression(array_literal.elements[2], 2, "*", 2)
    @test test_infixexpression(array_literal.elements[3], 3, "+", 3)
end

@testset "parser: index expressions" begin
    input = "myArray[1 + 1]"

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    index_expression = statement.expression
    @test typeof(index_expression) == IndexExpression

    @test test_identifier(index_expression.left, "myArray")

    @test test_infixexpression(index_expression.index, 1, "+", 1)
end

@testset "parser: hash literal" begin
    input = """
    {"one": 1, "two": 2, "three": 3}
    """

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    hash_literal = statement.expression
    @test typeof(hash_literal) == HashLiteral

    expected_values = Dict(
        "one" => 1,
        "two" => 2,
        "three" => 3,
    )

    @test length(hash_literal.pairs) == 3

    for (k, v) in hash_literal.pairs
        @test typeof(k) == StringLiteral
        @test test_integerliteral(v, expected_values[string(k)])
    end
end

@testset "parser: empty hash literal" begin
    input = """
    {}
    """

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    hash_literal = statement.expression
    @test typeof(hash_literal) == HashLiteral

    @test length(hash_literal.pairs) == 0
end

@testset "parser: hash literal with expressions" begin
    input = """
    {"one": 0 + 1, "two": 10 - 8, "three": 15 / 5}
    """

    lexer = Lexer(input)

    parser = Parser(lexer)

    program = parse_program!(parser)
    @assert check_parsererrors(parser)

    @test length(program) == 1

    statement = program.statements[1]
    @test typeof(statement) == ExpressionStatement

    hash_literal = statement.expression
    @test typeof(hash_literal) == HashLiteral

    @test length(hash_literal.pairs) == 3

    test_functions = Dict(
        "one" => function (e::Expression)
            test_infixexpression(e, 0, "+", 1)
        end,
        "two" => function (e::Expression)
            test_infixexpression(e, 10, "-", 8)
        end,
        "three" => function (e::Expression)
            test_infixexpression(e, 15, "/", 5)
        end,
    )

    for (k, v) in hash_literal.pairs
        @test typeof(k) == StringLiteral
        @test test_functions[string(k)](v)
    end
end
### _PARSER

### AST_
@testset "ast: test string()" begin
    program = Program(
        Vector{Statement}(
            [
            LetStatement(
                Token(LET, "let"),
                Identifier(Token(IDENT, "myVar"), "myVar"),
                Identifier(Token(IDENT, "anotherVar"), "anotherVar")
            )
        ]
        )
    )

    @test string(program) == "let myVar = anotherVar;"
end
### _AST

### EVALUATOR_

function test_eval(input::String)
    lexer = Lexer(input)
    parser = Parser(lexer)
    program = parse_program!(parser)
    env = Environment()

    eval(program, env)
end

function test_integerobject(object::Object, expected_value::Int)
    @assert typeof(object) == MonkeyInteger

    @assert object.value == expected_value

    true
end

function test_booleanobject(object::Object, expected_value::Bool)
    @assert typeof(object) == MonkeyBoolean

    @assert object.value == expected_value

    true
end

function test_nullobject(object::Object)
    @assert typeof(object) == MonkeyNull

    true
end

function test_arrayobject(object::Object, expected_value::Vector)
    @assert typeof(object) == MonkeyArray
    @assert length(object.elements) == length(expected_value)

    for (i, x) in enumerate(expected_value)
        @assert object.elements[i].value == x
    end

    true
end

@testset "evaluator: integer expression" begin
    struct IntegerEvalTest
        input::String
        expected_value::Int
    end

    tests = [
        IntegerEvalTest("5", 5),
        IntegerEvalTest("10", 10),
        IntegerEvalTest("-5", -5),
        IntegerEvalTest("-10", -10),
        IntegerEvalTest("5 + 5 + 5 + 5 - 10", 10),
        IntegerEvalTest("2 * 2 * 2 * 2 * 2", 32),
        IntegerEvalTest("-50 + 100 + -50", 0),
        IntegerEvalTest("5 * 2 + 10", 20),
        IntegerEvalTest("5 + 2 * 10", 25),
        IntegerEvalTest("20 + 2 * -10", 0),
        IntegerEvalTest("50 / 2 * 2 + 10", 60),
        IntegerEvalTest("2 * (5 + 10)", 30),
        IntegerEvalTest("3 * 3 * 3 + 10", 37),
        IntegerEvalTest("3 * (3 * 3) + 10", 37),
        IntegerEvalTest("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        @test test_integerobject(evaluated, test.expected_value)
    end
end

@testset "evaluator: string expression" begin
    input = "\"Hello World!\";"

    evaluated = test_eval(input)

    @test typeof(evaluated) == MonkeyString
    @test evaluated.value == "Hello World!"
end

@testset "evaluator: string concatenation" begin
    input = "\"Hello\" + \" \" + \"World!\""

    evaluated = test_eval(input)

    @test typeof(evaluated) == MonkeyString
    @test evaluated.value == "Hello World!"
end

@testset "evaluator: boolean expression" begin
    struct BooleanEvalTest
        input::String
        expected_value::Bool
    end

    tests = [
        BooleanEvalTest("true", true),
        BooleanEvalTest("false", false),
        BooleanEvalTest("1 < 2", true),
        BooleanEvalTest("1 > 2", false),
        BooleanEvalTest("1 < 1", false),
        BooleanEvalTest("1 > 1", false),
        BooleanEvalTest("1 == 1", true),
        BooleanEvalTest("1 != 1", false),
        BooleanEvalTest("1 == 2", false),
        BooleanEvalTest("1 != 2", true),
        BooleanEvalTest("true == true", true),
        BooleanEvalTest("false == false", true),
        BooleanEvalTest("true == false", false),
        BooleanEvalTest("true != false", true),
        BooleanEvalTest("false != true", true),
        BooleanEvalTest("(1 < 2) == true", true),
        BooleanEvalTest("(1 < 2) == false", false),
        BooleanEvalTest("(1 > 2) == true", false),
        BooleanEvalTest("(1 > 2) == false", true),
        BooleanEvalTest("(1 < 2) != true", false),
        BooleanEvalTest("(1 < 2) != false", true),
        BooleanEvalTest("(1 > 2) != true", true),
        BooleanEvalTest("(1 > 2) != false", false),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        @test test_booleanobject(evaluated, test.expected_value)
    end
end

@testset "evaluator: bang operator" begin
    struct BangEvalTest
        input::String
        expected_value::Bool
    end

    tests = [
        BangEvalTest("!true", false),
        BangEvalTest("!false", true),
        BangEvalTest("!5", false),
        BangEvalTest("!!true", true),
        BangEvalTest("!!false", false),
        BangEvalTest("!!5", true),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        @test test_booleanobject(evaluated, test.expected_value)
    end
end

@testset "evaluator: if-else expression" begin
    struct IfElseEvalTest{T}
        input::String
        expected_value::T
    end

    tests = [
        IfElseEvalTest("if (true) { 10 }", 10),
        IfElseEvalTest("if (false) { 10 }", nothing),
        IfElseEvalTest("if (1) { 10 }", 10),
        IfElseEvalTest("if (1 < 2) { 10 }", 10),
        IfElseEvalTest("if (1 > 2) { 10 }", nothing),
        IfElseEvalTest("if (1 > 2) { 10 } else { 20 }", 20),
        IfElseEvalTest("if (1 < 2) { 10 } else { 20 }", 10),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        if typeof(test.expected_value) == Int
            @test test_integerobject(evaluated, test.expected_value)
        else
            @test test_nullobject(evaluated)
        end
    end
end

@testset "evaluator: return statement" begin
    struct ReturnStatementEvalTest
        input::String
        expected_value::Int
    end

    tests = [
        ReturnStatementEvalTest("return 10;", 10),
        ReturnStatementEvalTest("return 10; 9;", 10),
        ReturnStatementEvalTest("return 2 * 5; 9;", 10),
        ReturnStatementEvalTest("9; return 2 * 5; 9;", 10),
        ReturnStatementEvalTest("""
        if (10 > 1) {
            if (10 > 1) {
                return 10;
            }
            return 1;
        }
        """, 10),
        ReturnStatementEvalTest("""
        fn(x) {
            if (x > 1) {
                return x;
            }
            return 0;
        }(1);
        return 10;
        """, 10),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        @test test_integerobject(evaluated, test.expected_value)
    end
end

@testset "evaluator: error handling" begin
    struct ErrorEvalTest
        input::String
        expected_message::String
    end

    tests = [
        ErrorEvalTest("5 + true;", "type mismatch: INTEGER + BOOLEAN"),
        ErrorEvalTest("5 + true; 5;", "type mismatch: INTEGER + BOOLEAN"),
        ErrorEvalTest("-true;", "unknown operator: BOOLEAN"),
        ErrorEvalTest("true + false;", "unknown operator: BOOLEAN + BOOLEAN"),
        ErrorEvalTest("5; true + false; 5;", "unknown operator: BOOLEAN + BOOLEAN"),
        ErrorEvalTest("if (10 > 1) { true + false; }", "unknown operator: BOOLEAN + BOOLEAN"),
        ErrorEvalTest("""
        if (10 > 1) {
            if (10 > 1) {
                return true + false;
            }
            return 1;
        }
        """,
            "unknown operator: BOOLEAN + BOOLEAN"),
        ErrorEvalTest("foobar", "identifier not found: foobar"),
        ErrorEvalTest("\"Hello\" - \"World\"", "unknown operator: STRING - STRING"),
        ErrorEvalTest("{\"name\": \"Monkey\"}[fn(x) { x }];", "unusable as hash key: FUNC"),
    ]

    for test in tests
        evaluated = test_eval(test.input)

        @test typeof(evaluated) == MonkeyError
        @test evaluated.message == test.expected_message
    end
end

@testset "evaluator: let statement" begin
    struct LetEvalTest
        input::String
        expected_value::Int
    end

    tests = [
        LetEvalTest("let a = 5; a;", 5),
        LetEvalTest("let a = 5 * 5; a;", 25),
        LetEvalTest("let a = 5; let b = a; b;", 5),
        LetEvalTest("let a = 5; let b = a; let c = a + b + 5; c;", 15),
    ]

    for test in tests
        @test test_integerobject(test_eval(test.input), test.expected_value)
    end
end

@testset "evaluator: function object" begin
    input = "fn(x) { x + 2; };"

    evaluated = test_eval(input)

    @test typeof(evaluated) == MonkeyFunction

    @test length(evaluated.parameters) == 1
    @test string(evaluated.parameters[1]) == "x"

    @test string(evaluated.body) == "(x + 2)"
end

@testset "evaluator: function application" begin
    struct FunctionEvalTest
        input::String
        expected_value::Int
    end

    tests = [
        FunctionEvalTest("let identity = fn(x) { x; }; identity(5);", 5),
        FunctionEvalTest("let identity = fn(x) { return x; }; identity(5);", 5),
        FunctionEvalTest("let double = fn(x) { x * 2; }; double(5);", 10),
        FunctionEvalTest("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
        FunctionEvalTest("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
        FunctionEvalTest("fn(x) { x; }(5)", 5),
    ]

    for test in tests
        @test test_integerobject(test_eval(test.input), test.expected_value)
    end
end

@testset "evaluator: closure" begin
    input = """
    let newAdder = fn(x) {
        fn(y) { x + y };
    };
    let addTwo = newAdder(2);
    addTwo(2);
    """

    @test test_integerobject(test_eval(input), 4)
end

@testset "evaluator: builtin function" begin
    struct BuiltinEvalTest{T}
        input::String
        expected::T
    end

    tests = [
        BuiltinEvalTest("len(\"\")", 0),
        BuiltinEvalTest("len(\"four\")", 4),
        BuiltinEvalTest("len(\"hello world\")", 11),
        BuiltinEvalTest("len(1)", "argument to 'len' not supported, got INTEGER"),
        BuiltinEvalTest("len(\"one\", \"two\")", "wrong number of arguments. got=2, want=1"),
        BuiltinEvalTest("first([1,2,3])", 1),
        BuiltinEvalTest("last([1,2,3])", 3),
        BuiltinEvalTest("rest([1,2,3])", [2, 3]),
        BuiltinEvalTest("push([1,2,3], 4)", [1, 2, 3, 4]),
    ]

    for test in tests
        evaluated = test_eval(test.input)

        if typeof(test.expected) == Int
            @test test_integerobject(evaluated, test.expected)
        elseif typeof(test.expected) == String
            @test typeof(evaluated) == MonkeyError
            @test evaluated.message == test.expected
        elseif typeof(test.expected) == Vector{Int}
            @test test_arrayobject(evaluated, test.expected)
        end
    end
end

@testset "evaluator: array literal" begin
    input = "[1, 2 * 2, 3 + 3]"

    evaluated = test_eval(input)
    @test typeof(evaluated) == MonkeyArray

    @test length(evaluated.elements) == 3

    @test test_integerobject(evaluated.elements[1], 1)
    @test test_integerobject(evaluated.elements[2], 4)
    @test test_integerobject(evaluated.elements[3], 6)
end

@testset "evaluator: array index expressions" begin
    struct ArrayIndexEvalTest{T}
        input::String
        expected::T
    end

    tests = [
        ArrayIndexEvalTest("[1, 2, 3][0]", 1),
        ArrayIndexEvalTest("[1, 2, 3][1]", 2),
        ArrayIndexEvalTest("[1, 2, 3][2]", 3),
        ArrayIndexEvalTest("let i = 0; [1][i]", 1),
        ArrayIndexEvalTest("[1, 2, 3][1 + 1];", 3),
        ArrayIndexEvalTest("let myArray = [1, 2, 3]; myArray[2];", 3),
        ArrayIndexEvalTest("let myArray = [1, 2, 3]; myArray[0] + myArray[1] + myArray[2];", 6),
        ArrayIndexEvalTest("let myArray = [1, 2, 3]; let i = myArray[0]; myArray[i];", 2),
        ArrayIndexEvalTest("[1, 2, 3][3]", nothing),
        ArrayIndexEvalTest("[1, 2, 3][-1]", nothing),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        if typeof(test.expected) == Int
            @test test_integerobject(evaluated, test.expected)
        else
            @test test_nullobject(evaluated)
        end
    end
end

@testset "evaluator: string hash key" begin
    hello1 = MonkeyString("Hello World")
    hello2 = MonkeyString("Hello World")
    diff1 = MonkeyString("My name is johnny")
    diff2 = MonkeyString("My name is johnny")

    @test hashkey(hello1) == hashkey(hello2)
    @test hashkey(diff1) == hashkey(diff2)
    @test hashkey(hello1) != hashkey(diff1)
end

@testset "evaluator: string hash key" begin
    one1 = MonkeyInteger(1)
    one2 = MonkeyInteger(1)
    two1 = MonkeyInteger(2)
    two2 = MonkeyInteger(2)

    @test hashkey(one1) == hashkey(one2)
    @test hashkey(two1) == hashkey(two2)
    @test hashkey(one1) != hashkey(two1)
end

@testset "evaluator: boolean hash key" begin
    @test hashkey(MONKEY_TRUE) == hashkey(MonkeyBoolean(true))
    @test hashkey(MONKEY_FALSE) == hashkey(MonkeyBoolean(false))
    @test hashkey(MONKEY_TRUE) != hashkey(MONKEY_FALSE)
end

@testset "evaluator: hash literal" begin
    input = """
    let two = "two";
    {
        "one": 10 - 9,
        two: 1 + 1,
        "thr" + "ee": 6 / 2,
        4: 4,
        true: 5,
        false: 6
    }
    """

    evaluated = test_eval(input)

    @test typeof(evaluated) == MonkeyHash

    expected::Dict{HashKey,Int} = Dict(
        hashkey(MonkeyString("one")) => 1,
        hashkey(MonkeyString("two")) => 2,
        hashkey(MonkeyString("three")) => 3,
        hashkey(MonkeyInteger(4)) => 4,
        hashkey(MONKEY_TRUE) => 5,
        hashkey(MONKEY_FALSE) => 6,
    )

    @test length(evaluated.pairs) == length(expected)

    for (expected_key, expected_value) in expected
        @test haskey(evaluated.pairs, expected_key)

        pair = evaluated.pairs[expected_key]

        test_integerobject(pair.value, expected_value)
    end
end

@testset "evaluator: hash index expressions" begin
    struct HashIndexEvalTest{T}
        input::String
        expected::T
    end

    tests = [
        HashIndexEvalTest("{\"foo\": 5}[\"foo\"]", 5),
        HashIndexEvalTest("{\"foo\": 5}[\"bar\"]", nothing),
        HashIndexEvalTest("let key = \"foo\"; {\"foo\": 5}[key]", 5),
        HashIndexEvalTest("{}[\"foo\"]", nothing),
        HashIndexEvalTest("{5: 5}[5]", 5),
        HashIndexEvalTest("{true: 5}[true]", 5),
        HashIndexEvalTest("{false: 5}[false]", 5),
    ]

    for test in tests
        evaluated = test_eval(test.input)
        if typeof(test.expected) == Int
            @test test_integerobject(evaluated, test.expected)
        else
            test_nullobject(evaluated)
        end
    end
end
### _EVALUATOR
