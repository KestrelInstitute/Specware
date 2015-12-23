(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

Set qualifying
spec
  import Polymorphic
  import /Library/PrettyPrinter/WadlerLindig

  op SetSTHashtable.emptySet : [a] Set a
  op SetSTHashtable.emptySet? : [a] Set a -> Bool

%  op SetSTHashtable.union : [a] Set a * Set a -> Set a
%  op SetSTHashtable.intersection : [a] Set a * Set a -> Set a
%  op SetSTHashtable.difference : [a] Set a * Set a -> Set a

  op SetSTHashtable.member? : [a] Set a * a -> Bool
  op SetSTHashtable.subset?: [a] Set a * Set a -> Bool

  op SetSTHashtable.delete : [a] Set a * a -> Set a
  op SetSTHashtable.insert : [a] Set a * a -> Set a

  op SetSTHashtable.find: [a] (a -> Bool) * Set a -> Option a

  %op SetSTHashtable.singleton : [a] a -> Set a

  op SetSTHashtable.fold : [a,b] (a -> b -> a) * a * Set b -> a
  op SetSTHashtable.map  : [a,b] (a -> b) * Set a -> Set b  

  op SetSTHashtable.to_List : [a] Set a -> List a

  def empty? s = SetSTHashtable.emptySet? s

  def member? l x = SetSTHashtable.member?(l,x)

  def subset? s1 s2 = SetSTHashtable.subset?(s1,s2)

  def empty = SetSTHashtable.emptySet

  def delete l x = SetSTHashtable.delete(l,x)

  def insert l a = SetSTHashtable.insert(l,a)

  def fold fl e l = SetSTHashtable.fold(fl,e,l)
  def map f s = SetSTHashtable.map(f,s)
  def find pred s = SetSTHashtable.find(pred,s)    
  def singleton x = SetSTHashtable.insert(SetSTHashtable.emptySet,x)

  def union s1 s2 = fold insert s1 s2
  def intersection s1 s2 = fold (fn result -> fn e1 ->
				 if member? s2 e1
				  then insert result e1
				  else result)
			     empty s1
  def difference s1 s2 = fold (fn result -> fn e1 ->
			       if member? s2 e1
				then result
				else insert result e1)
			   empty s1
  

%   def takeOne s =
%     case s of
% 	  | [] -> None
% 	  | h::t -> Some (h,t)

  def ppSet ppElem l =
     ppConcat [
       ppString "{",
       ppSep (ppString ",") (map ppElem (to_List l)),
       ppString "}"
     ]

  def toList s = SetSTHashtable.to_List s
  def fromList l = foldl (fn (r,e) -> insert r e) empty l
endspec
