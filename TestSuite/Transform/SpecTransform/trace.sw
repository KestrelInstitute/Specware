% ======================================================================
% Specs
% ======================================================================

A = spec
  type T
  op f : T -> T
end-spec

% ======================================================================
% built-in spec transform 'trace':
%   takes one argument: on, "on", off, or "off"
% ======================================================================

% ERROR: in transform: Unrecognized transform: trace
% FIXME: better error message - missing argument
TF_Bad_1 = transform A by {trace}

% ERROR: in transform: Trace on or off?
% argument is case sensitive
TF_Bad_2 = transform A by {trace On}

% ERROR: in transform: Trace on or off?
% argument is case sensitive
TF_Bad_3 = transform A by {trace "Off"}

TF_Good_1 = transform A by {trace on}

TF_Good_2 = transform A by {trace "off"}

