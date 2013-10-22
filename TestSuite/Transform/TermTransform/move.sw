% ======================================================================
% Specs
% ======================================================================

A = spec
  op g1(n: Int): (Int * Option Int)
  op g2(n: Int): Bool
  op f(n: Int): {r: Int | if ex (m, w) (m, Some w) = g1 n && r = m ** w && m > 2 then g2 r else true}
end-spec

% ======================================================================
% built-in spec transform 'move':
%   primitive movement:  move f                 (first)
%                        move l                 (last)
%                        move n                 (next)
%                        move p                 (prev)
%                        move w                 (widen)
%                        move a                 (all)
%                        move post              (post)
%   search movement:     move (s <string>)      (forward search)
%                        move (r <string>)      (reverse search)
%   multiple movements:  move (<move1>, <move2>, ...)
%                        move [<move1>, <move2>, ...]
% ======================================================================

% ERROR: in transform: Unrecognized move command: 1
TF_Bad_1 = transform A by {at f {move 1; simpIf}}

% ERROR: in transform: Unrecognized move command: s
TF_Bad_2 = transform A by {at f {move s "ex"; structureEx}}

% ERROR: in transform: Unrecognized move command: b
TF_Bad_3 = transform A by {at f {move (l, b "ex"); simpIf}}

% ERROR: in transform: Illegal search string
TF_Bad_4 = transform A by {at f {move (s 2); simpIf}}

TF_Good_1 = transform A by {at f {move f; simpIf}}

% search string does not need string quotes if it is an identifier
TF_Good_2 = transform A by {at f {move (s g1); structureEx}}

%
TF_Good_3 = transform A by {at f {move (s n); structureEx}}

% multiple movements in parentheses
TF_Good_4 = transform A by {at f {move (l, r "ex", w); simpIf}}

% multiple movements in brackets
TF_Good_5 = transform A by {at f {move [s "ex", w]; simpIf}}
