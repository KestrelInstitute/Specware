(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

spec

%% Note: This spec imports all specs in this library (General).  It
%% exists mainly for testing purposes.  When importing functionality
%% from this library, it is probably best to import only the specs
%% that you need, rather than importing this All.sw file.  This is for
%% two reasons: 1. Specware (and especially Isabelle) will be faster
%% will less stuff to load.  2.  This All.sw file may change as
%% libraries are added, moved, combined, etc.  So, if you import this
%% All.sw file, you might suddenly start getting more or different
%% stuff (possibly giving name clashes with your names or causing
%% other problems).

import AllIsa

% For each of these, I've added a comment about why we can't get its
% obligations through Isabelle:

%% This has name clashes with FiniteSet.  It also contains a quotient:
%import FiniteSetAsList

%%import FiniteSetAsListMorphism % imports FiniteSetAsList, which contains a quotient

%% Name clashes.  Also, ultimately depends on FiniteSetAsList, which contains a quotient:
%import FiniteMapAsList

%%import FiniteMapAsListMorphism % ultimately depends on FiniteSetAsList, which contains a quotient

%%import FiniteMapAsFiniteSetMorphism %error in Isabelle obligations

import Rational % contains a quotient
import Real % imports Rational, which contains a quotient
import TimedTrace % ultimately depends on Rational, which contains a quotient

end-spec
