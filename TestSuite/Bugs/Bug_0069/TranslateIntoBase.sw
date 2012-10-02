S = spec type MyChar = Char endspec

%% Note: {MyChar +-> Char} would work, because the new Char
%% would be unqualified Char, distinct from Char.Char
%% That is confusing, but not the concern of this test.

M = translate S by {MyChar +-> Char.Char}

