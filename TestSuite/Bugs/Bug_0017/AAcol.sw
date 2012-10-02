A = spec def fubaz = 12345 endspec

D = diagram { X +-> A, Y +-> A } % two nodes, X and Y, each labelled with A

C = colimit D % C should have two copies of A, hence two copies of fubaz
