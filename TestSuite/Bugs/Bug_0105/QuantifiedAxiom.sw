
%% Good...
A = spec
 op f infixl 22 : [a] List a * a -> Int
 def i = 123
 axiom A is ([i] f 3 = 0)
endspec

%% Error...
B = spec
 op f infixl 22 : [a] List a * a -> Int
 def i = 123
 axiom A is [i] f 3 = 0
endspec

%% Peculiar...
C = spec
 op f infixl 22 : [a] a -> Int
 def i = 123
 axiom A is [i] f 3 = 0
endspec

