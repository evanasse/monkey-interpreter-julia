import Base: string, length
include("token.jl")
include("object.jl")

### AST_
abstract type Node end

function tokenliteral(node::Node)
    node.token.literal
end

abstract type Statement <: Node end

abstract type Expression <: Node end

function string(expression::Expression)
    expression.token.literal
end

# Program
struct Program <: Node
    statements::Vector{Statement}
end

function tokenliteral(program::Program)
    if length(program.statements) > 0
        return tokenliteral(program.statements[0])
    end

    ""
end

function string(program::Program)
    map(string, program.statements) |> x -> join(x, "")
end

function length(program::Program)
    length(program.statements)
end


# Expressions
struct Identifier <: Expression
    token::Token
    value::String
end
struct IntegerLiteral <: Expression
    token::Token
    value::Int
end
struct StringLiteral <: Expression
    token::Token
    value::String
end
struct Boolean <: Expression
    token::Token
    value::Bool
end

struct PrefixExpression <: Expression
    token::Token
    operator::String
    right::Expression
end

function string(pe::PrefixExpression)
    "($(pe.operator)$(string(pe.right)))"
end

struct InfixExpression <: Expression
    token::Token
    left::Expression
    operator::String
    right::Expression
end

function string(ie::InfixExpression)
    "($(string(ie.left)) $(ie.operator) $(string(ie.right)))"
end

struct ArrayLiteral <: Expression
    token::Token
    elements::Array{Expression}
end

function string(al::ArrayLiteral)
    elements = map(string, al.elements) |> elements -> join(elements, ", ")

    "[$(elements)]"
end

struct BlockStatement <: Statement
    token::Token
    statements::Array{Statement}
end

function string(block::BlockStatement)
    out = ""

    for s in block.statements
        out = out * string(s)
    end

    out
end

struct IfExpression <: Expression
    token::Token
    condition::Expression
    consequence::BlockStatement
    alternative::Union{BlockStatement,Nothing}
end

function string(ie::IfExpression)
    out = "if $(string(ie.condition)) $(string(ie.consequence))"

    if !isnothing(ie.alternative)
        out = out * "else $(string(ie.alternative))"
    end

    out
end

struct FunctionLiteral <: Expression
    token::Token
    parameters::Array{Identifier}
    body::BlockStatement
end

function string(fl::FunctionLiteral)
    parameters = map(string, fl.parameters) |> params -> join(params, ", ")

    "$(tokenliteral(fl))($parameters) $(string(fl.body))"
end

struct CallExpression <: Expression
    token::Token
    func::Expression
    arguments::Array{Expression}
end

function string(ce::CallExpression)
    arguments = map(string, ce.arguments) |> arguments -> join(arguments, ", ")

    "$(string(ce.func))($arguments)"
end

struct IndexExpression <: Expression
    token::Token
    left::Expression
    index::Expression
end

function string(ie::IndexExpression)
    "($(string(ie.left))[$(string(ie.index))])"
end

struct HashLiteral <: Expression
    token::Token
    pairs::Dict{Expression,Expression}
end

function string(hl::HashLiteral)
    pairs = []

    for (k, v) in hl.pairs
        push!(pairs, "$k:$v")
    end

    "{$(join(pairs, ", "))}"
end

# Statements
struct LetStatement <: Statement
    # node::Node
    token::Token
    name::Identifier
    value::Union{Expression,Nothing}
end

function string(statement::LetStatement)
    value = if !isnothing(statement.value)
        string(statement.value)
    else
        ""
    end

    "$(tokenliteral(statement)) $(string(statement.name)) = $(value);"
end

struct ReturnStatement <: Statement
    token::Token
    return_value::Union{Expression,Nothing}
end

function string(statement::ReturnStatement)
    value = if !isnothing(statement.return_value)
        string(statement.return_value)
    else
        ""
    end

    "$(tokenliteral(statement)) $(value);"
end

struct ExpressionStatement <: Statement
    token::Token
    expression::Expression
end

function string(statement::ExpressionStatement)
    if !isnothing(statement.expression)
        string(statement.expression)
    else
        ""
    end
end

### _AST

### LEXER_
mutable struct Lexer
    input::String
    position::Int
    read_position::Int
    current_char::Char

    function Lexer(input, position=1, read_position=1, current_char=Char(0))
        lexer = new(input, position, read_position, current_char)

        readchar!(lexer)

        lexer
    end
end

function readchar!(lexer::Lexer)
    if lexer.read_position > length(lexer.input)
        lexer.current_char = Char(0)
    else
        lexer.current_char = lexer.input[lexer.read_position]
    end

    lexer.position = lexer.read_position
    lexer.read_position += 1

    lexer
end

function readstring!(lexer::Lexer)
    position = lexer.position + 1
    while true
        readchar!(lexer)
        if lexer.current_char == '"' || lexer.current_char == Char(0)
            break
        end
    end

    # -1 because Julia is 1 indexed
    lexer.input[position:lexer.position-1]
end

function isvalid_ident_char(c::Char)
    isletter(c) || c == '_'
end

function readidentifier!(lexer::Lexer)
    position = lexer.position

    while isvalid_ident_char(lexer.current_char)
        readchar!(lexer)
    end

    # -1 because Julia is 1 indexed
    lexer.input[position:lexer.position-1]
end

function readnumber!(lexer::Lexer)
    position = lexer.position

    while isdigit(lexer.current_char)
        readchar!(lexer)
    end

    # -1 because Julia is 1 indexed
    lexer.input[position:lexer.position-1]
end

function newtoken(token_type::Type{<:TokenType}, s)
    Token(token_type, string(s))
end

function skipwhitespace!(lexer::Lexer)
    whitespaces = [' ', '\t', '\n', '\r']

    while lexer.current_char in whitespaces
        readchar!(lexer)
    end
end

function peekchar(lexer::Lexer)
    if lexer.read_position >= length(lexer.input)
        return 0
    end

    lexer.input[lexer.read_position]
end

function nexttoken!(lexer::Lexer)
    skipwhitespace!(lexer)

    if lexer.current_char == '='
        if peekchar(lexer) == '='
            c = lexer.current_char
            readchar!(lexer)
            literal = string(c) * string(lexer.current_char)
            token = newtoken(EQ, literal)
        else
            token = newtoken(ASSIGN, lexer.current_char)
        end
    elseif lexer.current_char == ';'
        token = newtoken(SEMICOLON, lexer.current_char)
    elseif lexer.current_char == '('
        token = newtoken(LPAREN, lexer.current_char)
    elseif lexer.current_char == ')'
        token = newtoken(RPAREN, lexer.current_char)
    elseif lexer.current_char == ','
        token = newtoken(COMMA, lexer.current_char)
    elseif lexer.current_char == '+'
        token = newtoken(PLUS, lexer.current_char)
    elseif lexer.current_char == '-'
        token = newtoken(MINUS, lexer.current_char)
    elseif lexer.current_char == '!'
        if peekchar(lexer) == '='
            c = lexer.current_char
            readchar!(lexer)
            literal = string(c) * string(lexer.current_char)
            token = newtoken(NOT_EQ, literal)
        else
            token = newtoken(BANG, lexer.current_char)
        end
    elseif lexer.current_char == '/'
        token = newtoken(SLASH, lexer.current_char)
    elseif lexer.current_char == '*'
        token = newtoken(ASTERISK, lexer.current_char)
    elseif lexer.current_char == '<'
        token = newtoken(LT, lexer.current_char)
    elseif lexer.current_char == '>'
        token = newtoken(GT, lexer.current_char)
    elseif lexer.current_char == '{'
        token = newtoken(LBRACE, lexer.current_char)
    elseif lexer.current_char == '}'
        token = newtoken(RBRACE, lexer.current_char)
    elseif lexer.current_char == '['
        token = newtoken(LBRACKET, lexer.current_char)
    elseif lexer.current_char == ']'
        token = newtoken(RBRACKET, lexer.current_char)
    elseif lexer.current_char == '"'
        token = newtoken(STR, readstring!(lexer))
    elseif lexer.current_char == ':'
        token = newtoken(COLON, lexer.current_char)
    elseif lexer.current_char == Char(0)
        token = newtoken(EOF, Char(0))
    else
        if isvalid_ident_char(lexer.current_char)
            literal = readidentifier!(lexer)
            token = newtoken(lookupident(literal), literal)

            return token
        elseif isdigit(lexer.current_char)
            return newtoken(INT, readnumber!(lexer))
        else
            token = newtoken(ILLEGAL, lexer.current_char)
        end
    end

    readchar!(lexer)

    token
end
### _LEXER

### PARSER_
const PrefixParseFn = Function
const InfixParseFn = Function

@enum OpPrecedence begin
    LOWEST
    EQUALS
    LESSGREATER
    SUM
    PRODUCT
    PREFIX
    CALL
    INDEX
end

precedences = Dict(
    EQ => EQUALS,
    NOT_EQ => EQUALS,
    LT => LESSGREATER,
    GT => LESSGREATER,
    PLUS => SUM,
    MINUS => SUM,
    SLASH => PRODUCT,
    ASTERISK => PRODUCT,
    LPAREN => CALL,
    LBRACKET => INDEX,
)

mutable struct Parser
    lexer::Lexer
    current_token::Token
    peek_token::Token

    errors::Vector{String}

    function Parser(lexer)
        parser = new(
            lexer,
            Token(),
            Token(),
            Vector{String}(),
        )

        nexttoken!(parser)
        nexttoken!(parser)

        parser
    end
end

function peekprecedence(parser::Parser)
    if haskey(precedences, parser.peek_token.type)
        return precedences[parser.peek_token.type]
    end

    LOWEST::OpPrecedence
end

function currentprecedence(parser::Parser)
    if haskey(precedences, parser.current_token.type)
        return precedences[parser.current_token.type]
    end

    LOWEST::OpPrecedence
end

function peekerror!(parser::Parser, tokentype::Type{<:TokenType})
    message = "expected next token to be '$(tokentype)', got '$(parser.peek_token.type)' instead."

    push!(parser.errors, message)
end

function nexttoken!(parser::Parser)
    parser.current_token = parser.peek_token
    parser.peek_token = nexttoken!(parser.lexer)

    parser
end

function current_token_is(parser::Parser, tokentype::Type{<:TokenType})
    parser.current_token.type == tokentype
end

function peek_token_is(parser::Parser, tokentype::Type{<:TokenType})
    parser.peek_token.type == tokentype
end

function expectpeek!(parser::Parser, tokentype::Type{<:TokenType})
    if !peek_token_is(parser, tokentype)
        peekerror!(parser, tokentype)
        return false
    end

    nexttoken!(parser)
    true
end

function parse_letstatement!(parser::Parser)
    current_token = parser.current_token

    if !expectpeek!(parser, IDENT)
        return nothing
    end

    name = Identifier(parser.current_token, parser.current_token.literal)

    if !expectpeek!(parser, ASSIGN)
        return nothing
    end

    nexttoken!(parser)

    value = parse_expression!(parser, LOWEST::OpPrecedence)

    if peek_token_is(parser, SEMICOLON)
        nexttoken!(parser)
    end

    LetStatement(current_token, name, value)
end

function parse_returnstatement!(parser::Parser)
    current_token = parser.current_token

    nexttoken!(parser)

    return_value = parse_expression!(parser, LOWEST::OpPrecedence)

    if peek_token_is(parser, SEMICOLON)
        nexttoken!(parser)
    end

    ReturnStatement(current_token, return_value)
end

function parse_blockstatement!(parser::Parser)
    token = parser.current_token
    statements = []

    nexttoken!(parser)

    while !current_token_is(parser, RBRACE) && !current_token_is(parser, EOF)
        statement = parse_statement!(parser)
        if !isnothing(statement)
            push!(statements, statement)
        end
        nexttoken!(parser)
    end

    BlockStatement(token, statements)
end

function parse_functionparameters!(parser::Parser)
    identifiers = []

    if peek_token_is(parser, RPAREN)
        nexttoken!(parser)
        return identifiers
    end

    nexttoken!(parser)

    identifier = Identifier(parser.current_token, parser.current_token.literal)

    push!(identifiers, identifier)

    while peek_token_is(parser, COMMA)
        nexttoken!(parser)
        nexttoken!(parser)

        identifier = Identifier(parser.current_token, parser.current_token.literal)
        push!(identifiers, identifier)
    end

    if !expectpeek!(parser, RPAREN)
        return nothing
    end

    identifiers
end

function parse_prefixexpression!(parser::Parser, ::Type{IDENT})
    Identifier(parser.current_token, parser.current_token.literal)
end

function parse_prefixexpression!(parser::Parser, ::Type{STR})
    StringLiteral(parser.current_token, parser.current_token.literal)
end

function parse_prefixexpression!(parser::Parser, ::Union{Type{TRUE},Type{FALSE}})
    if parser.current_token.literal == "true"
        value = true
    elseif parser.current_token.literal == "false"
        value = false
    end

    Boolean(parser.current_token, value)
end

function parse_prefixexpression!(parser::Parser, ::Type{INT})
    current_token = parser.current_token

    value = 0
    try
        value = parse(Int, current_token.literal)
    catch
        push!(parser.errors, "could not parse '$(current_token.literal)' as integer")
        return nothing
    end

    IntegerLiteral(current_token, value)
end

function parse_prefixexpression!(parser::Parser, ::Union{Type{BANG},Type{MINUS}})
    token = parser.current_token
    operator = parser.current_token.literal

    nexttoken!(parser)

    right = parse_expression!(parser, PREFIX::OpPrecedence)

    PrefixExpression(token, operator, right)
end

function parse_prefixexpression!(parser::Parser, ::Union{Type{LPAREN},Type{RPAREN}})
    nexttoken!(parser)

    expression = parse_expression!(parser, LOWEST::OpPrecedence)

    if !expectpeek!(parser, RPAREN)
        return nothing
    end

    expression
end

function parse_prefixexpression!(parser::Parser, ::Type{LBRACKET})
    token = parser.current_token

    elements = parse_expressionlist!(parser, RBRACKET)

    ArrayLiteral(token, elements)
end

function parse_prefixexpression!(parser::Parser, ::Type{IF})
    token = parser.current_token

    if !expectpeek!(parser, LPAREN)
        return nothing
    end

    nexttoken!(parser)

    condition = parse_expression!(parser, LOWEST::OpPrecedence)

    if !expectpeek!(parser, RPAREN)
        return nothing
    end

    if !expectpeek!(parser, LBRACE)
        return nothing
    end

    consequence = parse_blockstatement!(parser)

    alternative = nothing

    if peek_token_is(parser, ELSE)
        nexttoken!(parser)

        if !expectpeek!(parser, LBRACE)
            return nothing
        end

        alternative = parse_blockstatement!(parser)
    end

    IfExpression(token, condition, consequence, alternative)
end

function parse_prefixexpression!(parser::Parser, ::Type{FUNCTION})
    token = parser.current_token

    if !expectpeek!(parser, LPAREN)
        return nothing
    end

    parameters = parse_functionparameters!(parser)

    if !expectpeek!(parser, LBRACE)
        return nothing
    end

    body = parse_blockstatement!(parser)

    FunctionLiteral(token, parameters, body)
end

function parse_prefixexpression!(parser::Parser, ::Type{LBRACE})
    token = parser.current_token
    pairs = Dict{Expression,Expression}()

    while !peek_token_is(parser, RBRACE)
        nexttoken!(parser)

        key = parse_expression!(parser, LOWEST::OpPrecedence)

        if !expectpeek!(parser, COLON)
            return nothing
        end

        nexttoken!(parser)

        value = parse_expression!(parser, LOWEST::OpPrecedence)

        pairs[key] = value

        if !peek_token_is(parser, RBRACE) && !expectpeek!(parser, COMMA)
            return nothing
        end
    end

    if !expectpeek!(parser, RBRACE)
        return nothing
    end

    HashLiteral(token, pairs)
end

function parse_infixexpression!(
    parser::Parser,
    left::Expression,
    ::Union{
        Type{PLUS},
        Type{MINUS},
        Type{SLASH},
        Type{ASTERISK},
        Type{EQ},
        Type{NOT_EQ},
        Type{LT},
        Type{GT},
    }
)
    token = parser.current_token
    operator = parser.current_token.literal

    precedence = currentprecedence(parser)

    nexttoken!(parser)

    right = parse_expression!(parser, precedence)

    InfixExpression(token, left, operator, right)
end

function parse_expressionlist!(parser::Parser, closing_token::Union{Type{RPAREN},Type{RBRACKET}})
    list = []

    if peek_token_is(parser, closing_token)
        nexttoken!(parser)
        return list
    end

    nexttoken!(parser)
    push!(list, parse_expression!(parser, LOWEST::OpPrecedence))

    while peek_token_is(parser, COMMA)
        nexttoken!(parser)
        nexttoken!(parser)

        push!(list, parse_expression!(parser, LOWEST::OpPrecedence))
    end

    if !expectpeek!(parser, closing_token)
        return nothing
    end

    return list
end

function parse_infixexpression!(parser::Parser, func::Expression, ::Type{LPAREN})
    token = parser.current_token
    arguments = parse_expressionlist!(parser, RPAREN)

    CallExpression(token, func, arguments)
end

function parse_infixexpression!(parser::Parser, left::Expression, ::Type{LBRACKET})
    token = parser.current_token

    nexttoken!(parser)

    index = parse_expression!(parser, LOWEST::OpPrecedence)

    if !expectpeek!(parser, RBRACKET)
        return nothing
    end

    IndexExpression(token, left, index)
end

function parse_expression!(parser::Parser, precedence::OpPrecedence)
    if !hasmethod(parse_prefixexpression!, Tuple{Parser,Type{parser.current_token.type}})
        println("/!\\ ERROR: No parse function found for '$(parser.current_token.literal)'.")
        return nothing
    end

    left_expression = parse_prefixexpression!(parser, parser.current_token.type)

    while !peek_token_is(parser, SEMICOLON) && precedence < peekprecedence(parser)
        if !hasmethod(parse_infixexpression!, Tuple{Parser,Expression,Type{parser.peek_token.type}})
            return left_expression
        end

        nexttoken!(parser)

        left_expression = parse_infixexpression!(parser, left_expression, parser.current_token.type)
    end

    left_expression
end

function parse_expressionstatement!(parser::Parser)
    current_token = parser.current_token
    expression = parse_expression!(parser, LOWEST::OpPrecedence)

    if peek_token_is(parser, SEMICOLON)
        nexttoken!(parser)
    end

    ExpressionStatement(current_token, expression)
end

function parse_statement!(parser::Parser)
    if parser.current_token.type == LET
        return parse_letstatement!(parser)
    elseif parser.current_token.type == RETURN
        return parse_returnstatement!(parser)
    else
        return parse_expressionstatement!(parser)
    end
end


function parse_program!(parser::Parser)
    statements = Vector{Statement}()

    while !current_token_is(parser, EOF)
        statement = parse_statement!(parser::Parser)
        if !isnothing(statement)
            push!(statements, statement)
        end

        nexttoken!(parser)
    end

    Program(statements)
end
### _PARSER

### EVALUATOR_

const MONKEY_NULL = MonkeyNull()
const MONKEY_TRUE = MonkeyBoolean(true)
const MONKEY_FALSE = MonkeyBoolean(false)



struct MonkeyFunction <: Object
    parameters::Array{Identifier}
    body::BlockStatement
    env::Environment
end

function inspect(f::MonkeyFunction)
    params = map(string, f.parameters) |> x -> join(x, ", ")

    "fn($(params)) {\n$(string(f.body))\n}"
end

function type(::MonkeyFunction)
    FUNC
end



struct HashPair <: Object
    key::Object
    value::Object
end

struct MonkeyHash <: Object
    pairs::Dict{HashKey,HashPair}
end

function inspect(h::MonkeyHash)
    pairs = []
    for (_, pair) in h.pairs
        push!(pairs, "$(inspect(pair.key)): $(inspect(pair.value))")
    end

    "{$(join(pairs, ", "))}"
end

function type(::MonkeyHash)
    HASH
end



function nativebool_to_monkeyboolean(input::Bool)
    if input
        return MONKEY_TRUE
    end

    MONKEY_FALSE
end


function eval_bang_operator_expression(right::Object)
    if right == MONKEY_TRUE
        return MONKEY_FALSE
    elseif right == MONKEY_FALSE
        return MONKEY_TRUE
    elseif right == MONKEY_NULL
        return MONKEY_TRUE
    end

    MONKEY_FALSE
end

function eval_minus_prefix_operator_expression(right::Object)
    if type(right) != INTEGER
        return MonkeyError("unknown operator: $(type(right))")
    end

    value = right.value

    MonkeyInteger(-value)
end

function eval_integer_infixexpression(operator::String, left::MonkeyInteger, right::MonkeyInteger)
    if operator == "+"
        return MonkeyInteger(left.value + right.value)
    elseif operator == "-"
        return MonkeyInteger(left.value - right.value)
    elseif operator == "*"
        return MonkeyInteger(left.value * right.value)
    elseif operator == "/"
        return MonkeyInteger(left.value / right.value)
    elseif operator == ">"
        return nativebool_to_monkeyboolean(left.value > right.value)
    elseif operator == "<"
        return nativebool_to_monkeyboolean(left.value < right.value)
    elseif operator == "=="
        return nativebool_to_monkeyboolean(left.value == right.value)
    elseif operator == "!="
        return nativebool_to_monkeyboolean(left.value != right.value)
    end

    MonkeyError("unknown operator: $(type(left)) $(operator) $(type(right))")
end

function eval_string_infixexpression(operator::String, left::MonkeyString, right::MonkeyString)
    if operator != "+"
        return MonkeyError("unknown operator: $(type(left)) $(operator) $(type(right))")
    end

    MonkeyString(left.value * right.value)
end

function eval_prefixexpression(operator::String, right::Object)
    if operator == "!"
        return eval_bang_operator_expression(right)
    elseif operator == "-"
        return eval_minus_prefix_operator_expression(right)
    end

    MonkeyError("unknown operator: $(operator)$(type(right))")
end

function eval_infixexpression(operator::String, left::Object, right::Object)
    if type(left) == INTEGER && type(right) == INTEGER
        return eval_integer_infixexpression(operator, left, right)
    elseif type(left) == STRING && type(right) == STRING
        return eval_string_infixexpression(operator, left, right)
    elseif operator == "=="
        return nativebool_to_monkeyboolean(left == right)
    elseif operator == "!="
        return nativebool_to_monkeyboolean(left != right)
    elseif type(left) != type(right)
        return MonkeyError("type mismatch: $(type(left)) $(operator) $(type(right))")
    end

    MonkeyError("unknown operator: $(type(left)) $(operator) $(type(right))")
end

function eval_ifexpression(ie::IfExpression, env::Environment)
    condition = eval(ie.condition, env)

    if iserror(condition)
        return condition
    end

    if istruthy(condition)
        return eval(ie.consequence, env)
    elseif !isnothing(ie.alternative)
        return eval(ie.alternative, env)
    end

    MONKEY_NULL
end

function eval_expressions(expressions::Array{Expression}, env::Environment)
    result::Array{Object} = []

    for expr in expressions
        evaluated = eval(expr, env)

        if iserror(evaluated)
            return [evaluated]
        end

        push!(result, evaluated)
    end

    result
end

function eval_array_indexexpression(array::MonkeyArray, index::MonkeyInteger)
    idx = index.value
    max = length(array.elements) - 1

    if idx < 0 || idx > max
        return MONKEY_NULL
    end

    # +1 because Julia is 1-indexed
    array.elements[idx+1]
end

function eval_hash_indexexpression(left::MonkeyHash, index::Object)
    try
        hashkey(index)
    catch
        return MonkeyError("unusable as hash key: $(type(index))")
    end

    if !haskey(left.pairs, hashkey(index))
        return MONKEY_NULL
    end

    left.pairs[hashkey(index)].value
end

function eval_indexexpression(left::Object, index::Object)
    if type(left) == ARRAY && type(index) == INTEGER
        return eval_array_indexexpression(left, index)
    elseif type(left) == HASH
        return eval_hash_indexexpression(left, index)
    else
        return MonkeyError("index operator not supported: $(type(left))")
    end
end

function applyfunction(func::Object, arguments::Array{Object})
    if typeof(func) == MonkeyFunction
        extended_env = extend_functionenv(func, arguments)
        evaluated = eval(func.body, extended_env)

        return unwrap_returnvalue(evaluated)
    elseif typeof(func) == MonkeyBuiltin
        return func.func(arguments...)
    else
        return MonkeyError("not a function: $(type(func))")
    end
end

function extend_functionenv(func::MonkeyFunction, arguments::Array{Object})
    env = Environment(func.env)

    for (i, param) in enumerate(func.parameters)
        set(env, param.value, arguments[i])
    end

    env
end

function unwrap_returnvalue(return_value::MonkeyReturnValue)
    return_value.value
end

function unwrap_returnvalue(object::Object)
    object
end


function istruthy(::MonkeyNull)
    false
end

function istruthy(b::MonkeyBoolean)
    if b == MONKEY_TRUE
        return true
    end

    false
end

function istruthy(::Object)
    true
end



function iserror(o::Object)
    if !isnothing(o)
        return type(o) == ERROR
    end

    false
end


function eval(node::Program, env::Environment)
    result = nothing

    for statement in node.statements
        result = eval(statement, env)

        if typeof(result) == MonkeyReturnValue
            return result.value
        elseif typeof(result) == MonkeyError
            return result
        end
    end

    result
end

function eval(node::BlockStatement, env::Environment)
    result = nothing

    for statement in node.statements
        result = eval(statement, env)

        if !isnothing(result)
            result_type = type(result)
        else
            result_type = Nothing
        end

        if result_type == RETURN_VALUE || result_type == ERROR
            return result
        end
    end

    result
end

function eval(node::ExpressionStatement, env::Environment)
    eval(node.expression, env)
end

function eval(node::IntegerLiteral, ::Environment)
    MonkeyInteger(node.value)
end

function eval(node::Boolean, ::Environment)
    nativebool_to_monkeyboolean(node.value)
end

function eval(node::StringLiteral, ::Environment)
    MonkeyString(node.value)
end

function eval(node::PrefixExpression, env::Environment)
    right = eval(node.right, env)

    if iserror(right)
        return right
    end

    eval_prefixexpression(node.operator, right)
end

function eval(node::InfixExpression, env::Environment)
    left = eval(node.left, env)

    if iserror(left)
        return left
    end

    right = eval(node.right, env)

    if iserror(right)
        return right
    end

    eval_infixexpression(node.operator, left, right)
end

function eval(node::IfExpression, env::Environment)
    eval_ifexpression(node, env)
end

function eval(node::ReturnStatement, env::Environment)
    value = eval(node.return_value, env)

    if iserror(value)
        return value
    end

    MonkeyReturnValue(value)
end

function eval(node::LetStatement, env::Environment)
    value = eval(node.value, env)

    if iserror(value)
        return value
    end

    set(env, node.name.value, value)

    nothing
end

function eval(node::Identifier, env::Environment)
    value = get(env, node.value)

    if haskey(builtins, node.value)
        return builtins[node.value]
    end

    if isnothing(value)
        return MonkeyError("identifier not found: $(node.value)")
    end

    value
end

function eval(node::FunctionLiteral, env::Environment)
    MonkeyFunction(node.parameters, node.body, env)
end

function eval(node::CallExpression, env::Environment)
    func = eval(node.func, env)

    if iserror(func)
        return func
    end

    arguments = eval_expressions(node.arguments, env)
    if length(arguments) == 1 && iserror(arguments[1])
        return arguments[1]
    end

    applyfunction(func, arguments)
end

function eval(node::ArrayLiteral, env::Environment)
    elements = eval_expressions(node.elements, env)

    if length(elements) == 1 && iserror(elements[1])
        return elements[1]
    end

    MonkeyArray(elements)
end

function eval(node::IndexExpression, env::Environment)
    left = eval(node.left, env)
    if iserror(left)
        return left
    end

    index = eval(node.index, env)
    if iserror(index)
        return index
    end

    eval_indexexpression(left, index)
end

function eval(node::HashLiteral, env::Environment)
    pairs::Dict{HashKey,HashPair} = Dict()

    for (key_node, value_node) in node.pairs
        key = eval(key_node, env)

        if iserror(key)
            return key
        end

        try
            hashkey(key)
        catch
            return MonkeyError("unusable as hash key: $(typeof(key))")
        end

        value = eval(value_node, env)

        if iserror(value)
            return value
        end

        hashed = hashkey(key)

        pairs[hashed] = HashPair(key, value)
    end

    MonkeyHash(pairs)
end
### _EVALUATOR
