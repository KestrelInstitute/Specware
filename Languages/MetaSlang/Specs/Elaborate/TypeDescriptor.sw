(* Copyright 2015 Kestrel Institute. See file LICENSE.text for license details *)

%% what's the proper qualifier for this??
%% right now, just XML uses this
XML qualifying spec

  %% IMPORT AS LITTLE AS POSSIBLE 

  %% This file is imported by applications, so anything this imports
  %%  must be available to the application.
  %% In particular, avoid importing any internals of specware itself.

  type IdDescriptor   = String
  type QIdDescriptor  = String * String
  type TermDescriptor = String

  %% A term of type TypeDescriptor will be accessible at runtime as the reflection of a type
  %% that was otherwise only present at compile-time.
  type TypeDescriptor = | Arrow        TypeDescriptor * TypeDescriptor
                        | Product      List (IdDescriptor * TypeDescriptor)
                        | CoProduct    List (IdDescriptor * Option TypeDescriptor)
                        | Quotient     TypeDescriptor * TermDescriptor              
                        | Subtype      TypeDescriptor * TermDescriptor              
                        | Base         QIdDescriptor * List TypeDescriptor
                        | Boolean
                        | TyVar        
                        | MetaTyVar    
                        | Bottom

  def MakeArrowTypeDescriptor     (x, y)      : TypeDescriptor = Arrow      (x, y)
  def MakeProductTypeDescriptor   fields      : TypeDescriptor = Product    fields
  def MakeCoProductTypeDescriptor fields      : TypeDescriptor = CoProduct  fields
  def MakeQuotientTypeDescriptor  (base, qq)  : TypeDescriptor = Quotient   (base, qq)
  def MakeSubtypeTypeDescriptor   (base, pp)  : TypeDescriptor = Subtype    (base, pp)
  def MakeBaseTypeDescriptor      (q,id,args) : TypeDescriptor = Base       ((q,id), args)
  def MakeBooleanTypeDescriptor   ()          : TypeDescriptor = Boolean    

  %% Does this belong here (for use by apps) or elsewhere (for use by just Specware itself) ?

  type TypeDescriptorExpansionTable = List (TypeDescriptor * TypeDescriptor)

  def expand_TypeDescriptor (sd : TypeDescriptor, table : TypeDescriptorExpansionTable) =
   let
      def aux sd =
	let possible_entry = findLeftmost (fn (x,_) -> x = sd) table in
	case possible_entry of
	  | None -> sd
	  | Some (_, expansion) ->
	    case expansion of
	      | Base     _      -> aux expansion
	      | Subtype  (x, _) -> aux x
	      | Quotient (x, _) -> aux x
	      | _               -> expansion
   in
     aux sd

  def print_TypeDescriptor (sd : TypeDescriptor) =
    case sd of
      | Arrow        (x,y) -> (print_TypeDescriptor x) ^ " -> " ^ (print_TypeDescriptor y)
      | Product      fields -> "{" ^ (foldl (fn (result,(id, sd)) -> 
					     let this = id ^ ": " ^ (print_TypeDescriptor sd) in
					     case result of
					       | "" -> this
					       | _ -> result ^ ", " ^ this)
				            ""
					    fields) ^ "}"
      | CoProduct    fields -> (foldl (fn (result,(id, possible_sd)) -> 
				       "| " ^ id ^ 
				       (case possible_sd of
					 | None -> " "
					 | Some sd -> print_TypeDescriptor sd))
				      ""
				      fields)
      | Quotient     (sd,tm) -> (print_TypeDescriptor sd) ^ "\\" ^ "???"
      | Subtype      (sd,tm) -> (print_TypeDescriptor sd) ^ "|" ^ "???"
      | Base         ((q,id), parms) -> ((if q = "<unqualified>" then "" else q ^ ".") ^
					 id ^
					 (case parms of
					   | [] -> ""
					   | _ -> "(" ^ (foldl (fn (result,sd) -> 
								let this = print_TypeDescriptor sd in
								case result of
								  | "" -> this
								  | _ -> result ^ ", " ^ this)
							       ""
							       parms) ^ 
					    ")"))
      | Boolean       -> "Bool"
      | TyVar         -> "type var"
      | MetaTyVar     -> "meta type var"
      | Bottom        -> "<bottom>"

endspec
