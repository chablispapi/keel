(comment) @comment
(string) @string
(number) @constant.numeric.integer
(boolean) @constant.builtin.boolean

(definition name: (identifier) @function)
(type_definition name: (constructor) @type)
(import module: (module_name) @namespace)

["def" "private"] @keyword.function
["data" "codata" "effect" "bitdata" "linear"] @keyword.storage.type
"import" @keyword.control.import
((keyword) @keyword.control.conditional (#any-of? @keyword.control.conditional "if" "then" "else" "case" "of"))
((keyword) @keyword.operator (#any-of? @keyword.operator "land" "lor" "lxor" "lsl" "lsr" "as"))
((keyword) @function.special (#eq? @function.special "main"))
(keyword) @keyword

(builtin_type) @type.builtin
(constructor) @constructor
(effect_variable) @type.parameter
(identifier) @variable
(operator) @operator
((punctuation) @punctuation.bracket (#any-of? @punctuation.bracket "(" ")" "{" "}" "[" "]"))
(punctuation) @punctuation.delimiter
