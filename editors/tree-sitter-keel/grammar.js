// Tree-sitter grammar for Keel (.kl), for syntax highlighting. It reads a file as a stream of
// tokens plus the few spots where context decides the colour (the name after def, data,
// import, ...), so a half-typed line never spoils the rest of the file. keelc's parser
// (ref/src/Keel/Parser.hs) is the real grammar.
//
// ponytail: block comments don't nest here (they do in keelc); needs an external scanner.

const intTypes = ['i8', 'i16', 'i32', 'i64', 'u8', 'u16', 'u32', 'u64'];

module.exports = grammar({
  name: 'keel',

  extras: $ => [/\s/, $.comment],
  word: $ => $.identifier,

  rules: {
    source_file: $ => repeat($._item),

    _item: $ => choice(
      $.definition,
      $.type_definition,
      $.import,
      $.keyword,
      $.boolean,
      $.number,
      $.string,
      $.character,
      $.builtin_type,
      $.constructor,
      $.effect_variable,
      $.identifier,
      $.operator,
      $.punctuation,
    ),

    definition: $ => seq(optional('private'), 'def', field('name', $.identifier)),
    type_definition: $ => seq(
      optional('private'),
      optional('linear'),
      choice('data', 'codata', 'effect', 'bitdata'),
      field('name', $.constructor),
    ),
    import: $ => seq('import', field('module', $.module_name)),
    module_name: $ => seq($.identifier, repeat(seq('.', $.identifier))),

    keyword: _ => choice(
      'main', 'forall', 'let', 'in', 'var', 'mut', 'if', 'then', 'else', 'case', 'of', 'cocase',
      'handle', 'with', 'box', 'unbox', 'land', 'lor', 'lxor', 'lsl', 'lsr', 'as', 'Free', 'Lin',
    ),
    boolean: _ => choice('true', 'false'),
    builtin_type: _ => choice('Box', 'Unit', 'Bool', ...intTypes),

    number: _ => token(seq(
      choice(/0x[0-9a-fA-F][0-9a-fA-F_]*/, /[0-9][0-9_]*/),
      optional(choice(...intTypes)),
    )),
    string: _ => /"([^"\\\n]|\\.)*"/,
    character: _ => /'([^'\\\n]|\\[^'\n]+)'/,
    comment: _ => token(choice(/--[^\n]*/, /\{-([^-]|-+[^-}])*-+\}/)),

    constructor: _ => /[A-Z][A-Za-z0-9_]*/,
    identifier: _ => /[a-z_][A-Za-z0-9_]*/,
    effect_variable: _ => /'[A-Za-z0-9_]+/,
    operator: _ => choice('-o', /[-+*=<>&|:%?!.\/\\@]+/),
    punctuation: _ => choice('(', ')', '{', '}', '[', ']', ',', ';'),
  },
});
