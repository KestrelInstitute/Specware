Java7 qualifying spec

import /Languages/Grammars/ContextFree
import /Library/IO/Unicode/UnicodeSig

%%% Java uses Unicode

type Java7.JavaToken               = UChar
type Java7.RHS        non_terminal = CFG.RHS                (JavaToken, non_terminal)
type Java7.Rule       non_terminal = CFG.Rule               (JavaToken, non_terminal)
type Java7.Directive  non_terminal = CFG.Directive          (JavaToken, non_terminal)
type Java7.Directives non_terminal = CFG.Directives         (JavaToken, non_terminal)
type Java7.Grammar    non_terminal = CFG.ContextFreeGrammar (JavaToken, non_terminal)

op [nt] token (char : Char) : RHS nt =
 Terminal (uchar char)

op [nt] keyword (key  : String) : RHS nt =
 Seq (map (fn char ->
             Terminal (uchar char))
          (explode key))


%%% ========================================================================
%%% Terminals
%%% ========================================================================

%% digits and letters

op [nt] digit_0   : RHS nt = token #0
op [nt] digit_1   : RHS nt = token #1
op [nt] digit_2   : RHS nt = token #2
op [nt] digit_3   : RHS nt = token #3
op [nt] digit_4   : RHS nt = token #4
op [nt] digit_5   : RHS nt = token #5
op [nt] digit_6   : RHS nt = token #6
op [nt] digit_7   : RHS nt = token #7
op [nt] digit_8   : RHS nt = token #8
op [nt] digit_9   : RHS nt = token #9

op [nt] lower_a   : RHS nt = token #a
op [nt] lower_b   : RHS nt = token #b
op [nt] lower_c   : RHS nt = token #c
op [nt] lower_d   : RHS nt = token #d
op [nt] lower_e   : RHS nt = token #e
op [nt] lower_f   : RHS nt = token #f

op [nt] lower_l   : RHS nt = token #l
op [nt] lower_p   : RHS nt = token #p
op [nt] lower_u   : RHS nt = token #u
op [nt] lower_x   : RHS nt = token #x

op [nt] upper_A   : RHS nt = token #A
op [nt] upper_B   : RHS nt = token #B
op [nt] upper_C   : RHS nt = token #C
op [nt] upper_D   : RHS nt = token #D
op [nt] upper_E   : RHS nt = token #E
op [nt] upper_F   : RHS nt = token #F

op [nt] upper_L   : RHS nt = token #L
op [nt] upper_P   : RHS nt = token #P
op [nt] upper_U   : RHS nt = token #U
op [nt] upper_X   : RHS nt = token #X

%% control characters

op [nt] backspace : RHS nt = token #\x08
op [nt] Sub       : RHS nt = token #\x26  % aka control-z
op [nt] LF        : RHS nt = token #\n    % aka newline
op [nt] CR        : RHS nt = token #\r    % aka return
op [nt] SP        : RHS nt = token #\s    % space
op [nt] HT        : RHS nt = token #\t    % horizontal tab
op [nt] FF        : RHS nt = token #\f    % form feed

%% brackets

op [nt] right_paren    : RHS nt = token #)
op [nt] left_paren     : RHS nt = token #(
op [nt] right_angle    : RHS nt = token #>
op [nt] left_angle     : RHS nt = token #<
op [nt] left_square    : RHS nt = token #[
op [nt] right_square   : RHS nt = token #]
op [nt] left_curly     : RHS nt = token #{
op [nt] right_curly    : RHS nt = token #}

%% misc punctuation

op [nt] ampersand      : RHS nt = token #&
op [nt] at_sign        : RHS nt = token #@
op [nt] backslash      : RHS nt = token #\\
op [nt] bar            : RHS nt = token #|
op [nt] carrot         : RHS nt = token #^
op [nt] colon          : RHS nt = token #:
op [nt] comma          : RHS nt = token #,
op [nt] dot            : RHS nt = token #.
op [nt] double_quote   : RHS nt = token #"
op [nt] equal_sign     : RHS nt = token #=
op [nt] exclamation    : RHS nt = token #!
op [nt] minus          : RHS nt = token #-
op [nt] percent        : RHS nt = token #%
op [nt] plus           : RHS nt = token #+
op [nt] question_mark  : RHS nt = token #?
op [nt] semicolon      : RHS nt = token #;
op [nt] single_quote   : RHS nt = token #'
op [nt] slash          : RHS nt = token #/
op [nt] star           : RHS nt = token #*
op [nt] tilde          : RHS nt = token #~
op [nt] underscore     : RHS nt = token #_

op [nt] any_unicode_char : RHS nt = token #0

end-spec
