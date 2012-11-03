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

import FiniteSetAsList
import FiniteSetAsListMorphism
import FiniteMapAsList
import FiniteMapAsListMorphism
import FiniteMapAsFiniteSet
import FiniteMapAsFiniteSetMorphism

import Rational
import Real
import TimedTrace
endspec
