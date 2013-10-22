% ======================================================================
% Specs
% ======================================================================

A = spec
  op g1(n: Int): Option(Option Int)
  op f1a(n: Int): {r: Int | ex (m: Int, y) Some(y) = g1 n && Some m = y && r = m ** 2}

  theorem ex_some is [a,b] fa(e, p) (ex(x:a,y:b) Some y = e && p(x,y)) = (case e of Some y -> ex(x) p(x,y) | _ -> false)
end-spec

B = spec 
  import A 
end-spec

% ======================================================================
% built in term transform 'lr'
% ======================================================================

% WARNING: Rule-shaped theorem ex_some1 unable to extract any rules!
% FIXME??? Should this be an error instead of a warning?
TF_Bad_1 = transform A by {at f1a {lr ex_some1}}

% ERROR: in transform: Id expected. (at "ex_some")
TF_Bad_2 = transform A by {at f1a {lr "ex_some"}}

TF_Good_1 = transform A by {at f1a {lr ex_some};
                            showSpec tf}

TF_Good_2 = transform B by {at f1a lr ex_some}








