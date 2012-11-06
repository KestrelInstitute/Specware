

===================
|Metaslang| Grammar
===================


.. COMMENT:  ***************************************************************** 

This appendix lists the grammar rules of the |Metaslang| specification
language. These rules are identical to those of the
Chapter on `Metaslang`_. They are brought together here, without additional text, for
easy reference.

.. COMMENT:  ***************************************************************** 

The Grammar Description Formalism
#################################

.. productionlist::
   wiffle: `waffle` [ `waffle_tail` ] | 
         : `piffle` { + `piffle` }*

.. productionlist:: 
   piffle: 1 | M { `piffle` }*

.. COMMENT:
.. ***************************************************************** 

The Grammar
###########


Models
======

.. productionlist::
  op: `op_name`

.. productionlist:: spec: `spec_form`

.. COMMENT:  ***************************************************************** 

Symbols and Names
=================

.. productionlist::
  symbol: `simple_name` | 
         : `literal` | 
         : `special_symbol`
  simple_name: `first_syllable` { _ `next_syllable` }*
  first_syllable: `first_word_syllable` | 
                : `non_word_syllable`
  next_syllable: `next_word_syllable` | 
               : `non_word_syllable`
  first_word_syllable: `word_start_mark` { `word_continue_mark` }*
  next_word_syllable: `word_continue_mark` { `word_continue_mark` }*
  word_start_mark: `letter`
  word_continue_mark: `letter` | 
                    : `decimal_digit` | 
                    : " | 
                    : ?
  letter: A | B |  C |  D | E | F | G | 
        : H | I | J | K | L | M | N | O | 
        : P | Q | R | S | T | U | V | 
        : W | X | Y | Z | a | b | 
        : c | d | e | f | g | h | 
        : i | j | k | l | m | n | 
        : o | p | q | r | s | t | 
        : u | v | w | x | y | z
  decimal_digit: 0 | 1 | 2 | 3 | 4 | 5 | 
               : 6 | 7 | 8 | 9
  non_word_syllable: `non_word_mark` { `non_word_mark` }*
  non_word_mark: ` | ~ | ! | @ | * | ^ | & | 
               : * | - | = | + | \ | "|" | : | 
               : < | < | / | " | ? 
  special_symbol: _ | ( | ) | "[" | "]" | "{" | "}" | 
                : ; | , | .

.. COMMENT:  ***************************************************************** 

Comments
========

.. productionlist::
  comment: `line_end_comment` | 
         : `block_comment`
  line_end_comment: % `line_end_comment_body`
  line_end_comment_body: `any_text_up_to_end_of_line`
  block_comment: (* `block_comment_body` *)
  block_comment_body: `any_text_including_newlines_and_nested_block_comments`

.. COMMENT:  ***************************************************************** 

Units
=====

.. productionlist::
  unit_definition: `unit_identifier` = `unit_term`
  unit_term: `spec_term` | `morphism_term` | `diagram_term` | 
           : `target_code_term` | `proof_term`
  specware_file_contents: `unit_term` | 
                        : `infile_unit_definition` { `infile_unit_definition` }*
  infile_unit_definition: `fragment_identifier` = `unit_term`
  fragment_identifier: `simple_name`

.. COMMENT:  ***************************************************************** 

Unit Identifiers
================

.. productionlist::
  unit_identifier: `swpath_based_path` | 
                 : `relative_path`
  swpath_based_path: / `relative_path`
  relative_path: { `path_element` / }* `path_element` [ # `fragment_identifier` ]
  path_element: `path_mark` { `path_mark` }*
  path_mark: `letter` | `decimal_digit` | ! | * | & | " | + | 
           : - | = | @ | ^ | ` | ~ | .

.. COMMENT:  ***************************************************************** 

Specs
=====

.. productionlist::
  spec_term: `unit_identifier` | 
           : `spec_form` | 
           : `spec_qualification` | 
           : `spec_translation` | 
           : `spec_substitution` | 
           : `diagram_colimit` | 
           : `obligator`

.. COMMENT:  ***************************************************************** 

Spec Forms
==========


.. productionlist::
  spec_form: spec { `declaration` }* endspec

.. COMMENT:  ***************************************************************** 

Qualifications
==============


.. productionlist::
  spec_qualification: `qualifier` qualifying `spec_term`
  qualifier: `simple_name`
  name: `simple_name` | 
      : `qualified_name`
  qualified_name: `qualifier` . `simple_name`

.. COMMENT:  ***************************************************************** 

Translations
============


.. productionlist::
  spec_translation: translate `spec_term` by `name_map`
  name_map: "{" [ `name_map_item` { , `name_map_item` }* ] "}"
  name_map_item: `type_name_map_item` | 
               : `op_name_map_item` | 
               : `wildcard_map_item`
  type_name_map_item: [ type ] `name` +-> `name`
  op_name_map_item: [ op ] `annotable_name` +-> `annotable_name`
  annotable_name: `name` [ `type_annotation` ]
  type_annotation: : `type_descriptor`
  wildcard_map_item: `wildcard` +-> `wildcard`
  wildcard: `simple_wildcard` | 
          : `qualified_wildcard`
  simple_wildcard: _
  qualified_wildcard: `qualifier` . `simple_wildcard`

.. COMMENT:  ***************************************************************** 

Substitutions
=============


.. productionlist::
  spec_substitution: `spec_term` "[" `morphism_term` "]"

.. COMMENT:  ***************************************************************** 

Diagram Colimits
================


.. productionlist::
  diagram_colimit: colimit `diagram_term`

.. COMMENT:  ***************************************************************** 

Obligators
==========


.. productionlist::
  obligator: obligations `unit_term`

.. COMMENT:  ***************************************************************** 

Morphisms
=========

.. productionlist::
  morphism_term: `unit_identifier` | 
               : `spec_morphism`
  spec_morphism: morphism `spec_term` -> `spec_term` `name_map`

.. COMMENT:  ***************************************************************** 

Diagrams
========

.. productionlist::
  diagram_term: `unit_identifier` | 
              : `diagram_form`
  diagram_form: diagram "{" `diagram_element` { , `diagram_element` }* "}"
  diagram_element: `diagram_node` | 
                 : `diagram_edge`
  diagram_node: `simple_name` +-> `spec_term`
  diagram_edge: `simple_name` : `simple_name` -> `simple_name` +-> `morphism_term`

.. COMMENT:  ***************************************************************** 

Target Code Terms
=================

.. productionlist::
  target_code_term: generate `target_language_name` `spec_term` [ `generate_option` ]
  generate_option: in `string_literal` | 
                 : with `unit_identifier`
  target_language_name: c | 
                      : java | 
                      : lisp

.. COMMENT:  ***************************************************************** 

Proof Terms
===========

.. productionlist::
  proof_term: prove `claim_name` in `spec_term`
            :       [ with `prover_name` ]
            :       [ using `claim_list` ] :
            :       [ options `prover_options` ]
  prover_name: snark
  claim_list: `claim_name` { , `claim_name` }*
  prover_options: `string_literal`

.. COMMENT:  ***************************************************************** 

Declarations
============

.. productionlist::
  declaration: `import_declaration` | `type_declaration` | 
             : `op_declaration` | `claim_declaration` | 
             : `definition`
  definition: `type_definition` | `op_definition`
  equals: is | =

.. COMMENT:  ***************************************************************** 

Import-declarations
===================

.. productionlist::
  import_declaration: import `spec_term` { , `spec_term` }*

.. COMMENT:  ***************************************************************** 

Type-declarations
=================

.. productionlist::
  type_declaration: type `type_name` [ `formal_type_parameters` ] 
                  :  [ `equals` `old_or_new_type_descriptor` ]
  formal_type_parameters: `local_type_variable` | 
                        : ( `local_type_variable_list` )
  local_type_variable: `simple_name`
  local_type_variable_list: `local_type_variable` { , `local_type_variable` }*
  old_or_new_type_descriptor: `type_descriptor` | 
                            : `new_type_descriptor`

.. COMMENT:  ***************************************************************** 

Type-definitions
================

.. productionlist::
  type_definition: `type_abbreviation` | 
                 : `new_type_definition`
  type_abbreviation: def [ type ] `type_name` [ `formal_type_parameters` ] 
                   : `equals` `type_descriptor`
  new_type_definition: def [ type ] `type_name` [ `formal_type_parameters` ] 
                     : `equals` `new_type_descriptor`

.. COMMENT:  ***************************************************************** 

Op-declarations
===============

.. productionlist::
  op_declaration: op [ `type_variable_binder` ] `formal_expression` 
                :    [ `fixity` ] `type_annotation` [ `equals` `expression` ] | 
                : op `formal_expression` [ `fixity` ] `polytype_annotation`
                :    [ `equals` `expression` ]
  polytype_annotation: : `type_variable_binder` `type_descriptor`
  type_variable_binder: "[" `local_type_variable_list` "]"
  formal_expression: `op_name` | 
                   : `formal_application`
  formal_application: `formal_application_head` `formal_parameter`
  formal_application_head: `op_name` | 
                         : `formal_application`
  formal_parameter: `closed_pattern` | 
                  : "(" `pattern` "|" `expression` ")"
  fixity: `associativity` `priority`
  associativity: infixl | 
               : infixr
  priority: `nat_literal`

.. COMMENT:  ***************************************************************** 

Op-definitions
==============

.. productionlist::
  op_definition: def [ op ] [ `type_variable_binder` ] `formal_expression` 
               :     [ `type_annotation` ]  `equals` `expression` | 
               : def [ op ] `formal_expression` `polytype_annotation` `equals` `expression`

.. COMMENT:  ***************************************************************** 

Claim-declarations
==================

.. productionlist::
  claim_declaration: `claim_kind` `claim_name` is `claim` [ `proof_script` ]
  claim_kind: axiom | theorem | conjecture
  claim_name: `name`
  claim: [ `type_variable_binder` ] `expression`

.. COMMENT:  ***************************************************************** 

Type-descriptors
================

.. productionlist::
  type_descriptor: `type_arrow` | `slack_type_descriptor`
  new_type_descriptor: `type_sum` | `type_quotient`
  slack_type_descriptor: `type_product` | `tight_type_descriptor`
  tight_type_descriptor: `type_instantiation` | `closed_type_descriptor`
  closed_type_descriptor: `type_name` | Boolean | 
                        : `local_type_variable` | `type_record` | 
                        : `type_restriction` | `type_comprehension` | 
                        : ( `type_descriptor` )

.. COMMENT:  ***************************************************************** 

Type-sums
=========

.. productionlist::
  type_sum: `type_summand` { `type_summand` }*
  type_summand: "|" `constructor` [ `slack_type_descriptor` ]
  constructor: `simple_name`

.. COMMENT:  ***************************************************************** 

Type-arrows
===========

.. productionlist::
  type_arrow: `arrow_source` -> `type_descriptor`
  arrow_source: `type_sum` | 
              : `slack_type_descriptor`

.. COMMENT:  ***************************************************************** 

Type-products
=============

.. productionlist::
  type_product: `tight_type_descriptor` * `tight_type_descriptor`
              :  { * `tight_type_descriptor` }*

.. COMMENT:  ***************************************************************** 

Type-instantiations
===================

.. productionlist::
  type_instantiation: `type_name` `actual_type_parameters`
  actual_type_parameters: `closed_type_descriptor` | 
                        : ( `proper_type_list` )
  proper_type_list: `type_descriptor` , `type_descriptor` { , `type_descriptor` }*

.. COMMENT:  ***************************************************************** 

Type-names
==========

.. productionlist::
  type_name: `name`

.. COMMENT:  ***************************************************************** 

Type-records
============

.. productionlist::
  type_record: "{" [ `field_typer_list` ] "}" | 
             : ( )
  field_typer_list: `field_typer` { , `field_typer` }*
  field_typer: `field_name` `type_annotation`
  field_name: `simple_name`

.. COMMENT:  ***************************************************************** 

Type-restrictions
=================

.. productionlist::
  type_restriction: ( `slack_type_descriptor` "|" `expression` )

.. COMMENT:  ***************************************************************** 

Type-comprehensions
===================

.. productionlist::
  type_comprehension: "{" `annotated_pattern` "|" `expression` "}"

.. COMMENT:  ***************************************************************** 

Type-quotients
==============

.. productionlist::
  type_quotient: `closed_type_descriptor` / `closed_expression`

.. COMMENT:  ***************************************************************** 

Expressions
===========

.. productionlist::
  expression: `lambda_form` | `case_expression` | `let_expression` | 
            : `if_expression` | `quantification` | `unique_solution` | 
            : `annotated_expression` | `tight_expression`
  tight_expression: `application` | `closed_expression`
  closed_expression: `op_name` | `local_variable` | `literal` | 
                   : `field_selection` | `tuple_display` | `record_display` | 
                   : `sequential_expression` | `list_display` | `monadic_expression` | 
                   : `structor` | ( `expression` ) | ( `inbuilt_op` )
  inbuilt_op: `inbuilt_prefix_op` | 
            : `inbuilt_infix_op`
  inbuilt_prefix_op: ~
  inbuilt_infix_op: <=< | 
                  : =< | 
                  : "|'|" | 
                  : && | 
                  : = | 
                  : ~= | 
                  : |lt||lt|

.. COMMENT:  ***************************************************************** 

Lambda-forms
============

.. productionlist::
  lambda_form: fn `match`

.. COMMENT:  ***************************************************************** 

Case-expressions
================

.. productionlist::
  case_expression: case `expression` of `match`

.. COMMENT:  ***************************************************************** 

Let-expressions
===============

.. productionlist::
  let_expression: let `let_bindings` in `expression`
  let_bindings: `recless_let_binding` | 
              : `rec_let_binding_sequence`
  recless_let_binding: `pattern` `equals` `expression`
  rec_let_binding_sequence: `rec_let_binding` { `rec_let_binding` }*
  rec_let_binding: def `simple_name` `formal_parameter_sequence` 
                 : [ `type_annotation` ] `equals` `expression`
  formal_parameter_sequence: `formal_parameter` { `formal_parameter` }*

.. COMMENT:  ***************************************************************** 

If-expressions
==============

.. productionlist::
  if_expression: if `expression` then `expression` else `expression`

.. COMMENT:  ***************************************************************** 

Quantifications
===============

.. productionlist::
  quantification: `quantifier` ( `local_variable_list` ) `expression`
  quantifier: fa | ex | ex1
  local_variable_list: `annotable_variable` { , `annotable_variable` }*
  annotable_variable: `local_variable` [ `type_annotation` ]
  local_variable: `simple_name`

.. COMMENT:  ***************************************************************** 

Unique-solutions
================

.. productionlist::
  unique_solution: the ( `local_variable_list` ) `expression`

.. COMMENT:  ***************************************************************** 

Annotated-expressions
=====================

.. productionlist::
  annotated_expression: `tight_expression` `type_annotation`

.. COMMENT:  ***************************************************************** 

Applications
============

.. productionlist::
  application: `prefix_application` | 
             : `infix_application`
  prefix_application: `application_head` `actual_parameter`
  application_head: `closed_expression` | `inbuilt_prefix_op` | `prefix_application`
  actual_parameter: `closed_expression`
  infix_application: `operand` `infix_operator` `operand`
  operand: `tight_expression`
  infix_operator: `op_name` | `inbuilt_infix_op`

.. COMMENT:  ***************************************************************** 

Op-names
========

.. productionlist::
  op_name: `name`

.. COMMENT:  ***************************************************************** 

Literals
========

.. productionlist::
  literal: `boolean_literal` | `nat_literal` | `char_literal` | `string_literal`

.. COMMENT:  ***************************************************************** 

Boolean-literals
================

.. productionlist::
  boolean_literal: true | false

.. COMMENT:  ***************************************************************** 

Nat-literals
============

.. productionlist::
  nat_literal: `decimal_digit`     { `decimal_digit` }* | 
             : 0 X `hexadecimal_digit` { `hexadecimal_digit` }* | 
             : 0 x `hexadecimal_digit` { `hexadecimal_digit` }* | 
             : 0 O `octal_digit`       { `octal_digit`  }* | 
             : 0 o `octal_digit`       { `octal_digit`  }* | 
             : 0 B `binary_digit`      { `binary_digit` }* | 
             : 0 b `binary_digit`      { `binary_digit` }*
  hexadecimal_digit: `decimal_digit` | 
                   : a | b | c | d | e | f | A | 
                   : B | C | D | E | F 
  octal_digit: 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7
  binary_digit: 0 | 1

.. COMMENT:  ***************************************************************** 

Char-literals
=============

.. productionlist::
  char_literal: #`char_literal_glyph`
  char_literal_glyph: `char_glyph` | 
                    : "
  char_glyph: `letter` | 
            : `decimal_digit` | 
            : `other_char_glyph`
  other_char_glyph: ! | : | @ | # | $ | % | ^ | 
                  : & | * | ( | ) | _ | - | + | 
                  : = | "|" | ~ | ` | . | , | < | 
                  : < | ? | / | ; | " | "[" | "]" | 
                  : "{" | "}" | \\ | \" | \a | \b | \t | 
                  : \n | \v | \f | \r | \s | 
                  : \x `hexadecimal_digit` `hexadecimal_digit` 
.. COMMENT:  ***************************************************************** 

String-literals
===============

.. productionlist::
  string_literal: " `string_body` "
  string_body: { `string_literal_glyph` }*
  string_literal_glyph: `char_glyph` | 
                      : `significant_whitespace`
  significant_whitespace: `space` | `tab` | `newline`

.. COMMENT:  ***************************************************************** 

Field-selections
================

.. productionlist::
  field_selection: `closed_expression` . `field_selector`
  field_selector: `nat_literal` | 
                : `field_name`

.. COMMENT:  ***************************************************************** 

Tuple-displays
==============

.. productionlist::
  tuple_display: ( `tuple_display_body` )
  tuple_display_body: [ `expression` , `expression` { , `expression` }* ]

.. COMMENT:  ***************************************************************** 

Record-displays
===============

.. productionlist::
  record_display: "{" `record_display_body` "}"
  record_display_body: [ `field_filler` { , `field_filler` }* ]
  field_filler: `field_name` `equals` `expression`

.. COMMENT:  ***************************************************************** 

Sequential-expressions
======================

.. productionlist::
  sequential_expression: ( `open_sequential_expression` )
  open_sequential_expression: `void_expression` ; `sequential_tail`
  void_expression: `expression`
  sequential_tail: `expression` | `open_sequential_expression`

.. COMMENT:  ***************************************************************** 

List-displays
=============

.. productionlist::
  list_display: "[" `list_display_body` "]"
  list_display_body: [ `expression` { , `expression` }* ]

.. COMMENT:  ***************************************************************** 

Monadic-expressions
===================

.. productionlist::
  monadic_expression: "{" `open_monadic_expression` "}"
  open_monadic_expression: `monadic_statement` ; `monadic_tail`
  monadic_statement: `expression` | 
                   : `monadic_binding`
  monadic_binding: `pattern` <- `expression`
  monadic_tail: `expression` | 
              : `open_monadic_expression`

.. COMMENT:  ***************************************************************** 

Structors
=========

.. productionlist::
  structor: `projector` | `quotienter` | `chooser` | `embedder` | `embedding_test`

.. productionlist:: projector: project `field_selector`

.. productionlist::
  quotienter: quotient "[" `type_name` "]"

.. productionlist:: chooser: choose "[" `type_name` "]"

.. productionlist::
  embedder: [ embed ] `constructor`

.. productionlist:: embedding_test: embed? `constructor`

.. COMMENT:  ***************************************************************** 

Matches
=======

.. productionlist::
  match: [ "|" ] `branch` { "|" `branch` }*
  branch: `pattern` [ `guard` ] -> `expression`
  guard: "|" `expression`

.. COMMENT:  ***************************************************************** 

Patterns
========

.. productionlist::
  pattern: `annotated_pattern` | 
         : `tight_pattern`
  tight_pattern: `aliased_pattern` | 
               : `cons_pattern` | 
               : `embed_pattern` | 
               : `quotient_pattern` | 
               : `closed_pattern`
  closed_pattern: `variable_pattern` | 
                : `wildcard_pattern` | 
                : `literal_pattern` | 
                : `list_pattern` | 
                : `tuple_pattern` | 
                : `record_pattern` | 
                : ( `pattern` )

.. productionlist:: 
  annotated_pattern: `pattern` `type_annotation`
  aliased_pattern: `variable_pattern` as `tight_pattern` 
  cons_pattern: `closed_pattern` :: `tight_pattern` 
  embed_pattern: `constructor` [`closed_pattern` ] 
  quotient_pattern: quotient "[" `type_name` "]"
  variable_pattern: `local_variable` wildcard_pattern: _
  literal_pattern: `literal` 
  list_pattern: "[" `list_pattern_body` "]"
  list_pattern_body: [ `pattern` { , `pattern` }* ] 
  tuple_pattern: ( `tuple_pattern_body` ) 
  tuple_pattern_body: [ `pattern` , `pattern` { ,`pattern` }* ] 
  record_pattern: "{" `record_pattern_body` "}"
  record_pattern_body: [ `field_patterner` { , `field_patterner` }* ]
  field_patterner: `field_name` [ `equals` `pattern` ]

.. COMMENT:  ***************************************************************** 




