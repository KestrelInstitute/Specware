(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)


XML qualifying spec

  import Parse_Document
  import TemporaryHack

  %%% ================================================================================
  %%%
  %%% Grammar conventions:
  %%%
  %%%   The grammar used here is based on the grammar specified by rules [1]-[85],
  %%%   (but note there are no rules 33-38 or 79), found at
  %%%
  %%%       http://www.w3.org/TR/REC-xml#sec-documents
  %%%
  %%%   and quoted in XML_Sig.sw, including associated conditions tagged as one of:
  %%%
  %%%     WFC : Well-formedness constraint
  %%%     VC  : Validity constraint
  %%%
  %%%   A straightforward implementation of the W3 grammar is possible, but would
  %%%   be less than ideal.  In particular, it would be poor at identifying simple
  %%%   typos and misspellings, or noticing that attrs were specified, but out of
  %%%   order, etc.
  %%%
  %%%   Accordingly, we introduce Kestrel specific productions, labelled [K1] .. [K39]
  %%%   which are implemented here to factor some original W3 ruls into a parsing
  %%%   stage using KI rules followed by post-parsing well formedness checks based
  %%%   perhaps on other W3 rules.
  %%%
  %%%   All such substitutions are clearly indicated, and the required well-formedness
  %%%   checks are indicated by KWFC and KVC annotations, analogous to WFC and VC annotations.
  %%%
  %%%   Original W3 rules that are replaced by KI rules are flagged with an asterisk,
  %%%   whereever they are referenced.
  %%%
  %%% ================================================================================
  %%%
  %%% Coding style:
  %%%
  %%%  This parser is written using a simple exception/io monad, for three reasons:
  %%%
  %%%  (1) The grammar requires very little backtracking, hence is readily implemented
  %%%      as a mainly linear flow of control with some dispatches based on
  %%%      lookahead of just a few characters, which is easily handled by metaslang
  %%%      pattern matching on lists..
  %%%
  %%%  (2) An exception monad enables an orderly(*) termination of parsing via a
  %%%      failure function without visually or conceptually cluttering the normal
  %%%      flow of control.
  %%%
  %%%  (3) An IO monad permits us to accumulate warnings and error messages in an
  %%%      orderly manner, again without cluttering the normal flow.
  %%%
  %%%      [* I.e., without side effects or non-local control jumps.]
  %%%
  %%%  Note that some monadic grammars are used to facilitate back-tracking via
  %%%  continuations.  That is explicitly NOT the case here, since this can be
  %%%  extremely (exponentially!) inefficient and can lead to very confusing
  %%%  error messags.
  %%%
  %%% ================================================================================
  %%%
  %%% Naming Convention:
  %%%
  %%%  start refers to the list of original chars at the start of a routine.
  %%%  tail  refers to the list just beyond the last successfully parsed character.
  %%%  scout refers to a point beyond the tail which is reached only tentatively.
  %%%
  %%%  We may return  (None,     start)
  %%%             or  (Some xxx, tail)
  %%%
  %%%  but we never return a scouted position.
  %%%
  %%%  Local routines named probe are eagerly looking for a sequence of as many
  %%%  things as they can find, but are prepared to return happily at the current
  %%%  tail as soon as they cannot find any more.  Often they terminate by looking
  %%%  for some kind of closing bracket: >)]
  %%%
  %%% ================================================================================

endspec
