% the following morphism witnesses (once its proof obligations are
% discharged) that BagsAsLists is indeed a refinement of Bags

morphism Bags -> BagsAsLists 
         {Bag +-> Bag,
          \/  +-> bag_union,
          --  +-> bag_difference}

% proof obligations:
% the axioms characterizing the operations in Bags are satisfied
% by the definitions of those operations in BagsAsLists
