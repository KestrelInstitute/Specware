%% what's the proper qualifier for this??
%% right now, just XML uses this
XML qualifying spec

  %% IMPORT AS LITTLE AS POSSIBLE 

  %% This file is imported by applications, so anything this imports
  %%  must be available to the application.
  %% In particular, avoid importing any internals of specware itself.

  sort IdDescriptor   = String
  sort QIdDescriptor  = String * String
  sort TermDescriptor = String

  %% A term of type SortDescriptor will be accessible at runtime as the reflection of a sort
  %% that was otherwise only present at compile-time.
  sort SortDescriptor = | Arrow        SortDescriptor * SortDescriptor
                        | Product      List (IdDescriptor * SortDescriptor)
                        | CoProduct    List (IdDescriptor * Option SortDescriptor)
                        | Quotient     SortDescriptor * TermDescriptor              
                        | Subsort      SortDescriptor * TermDescriptor              
                        | Base         QIdDescriptor * List SortDescriptor
                        | TyVar        
                        | MetaTyVar    
                        | Bottom

  def MakeArrowSortDescriptor     (x, y)      : SortDescriptor = Arrow      (x, y)
  def MakeProductSortDescriptor   fields      : SortDescriptor = Product    fields
  def MakeCoProductSortDescriptor fields      : SortDescriptor = CoProduct  fields
  def MakeQuotientSortDescriptor  (base, qq)  : SortDescriptor = Quotient   (base, qq)
  def MakeSubsortSortDescriptor   (base, pp)  : SortDescriptor = Subsort    (base, pp)
  def MakeBaseSortDescriptor      (q,id,args) : SortDescriptor = Base       ((q,id), args)

endspec