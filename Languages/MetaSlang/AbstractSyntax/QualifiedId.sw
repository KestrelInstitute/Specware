(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

MetaSlang qualifying spec
import /Library/Legacy/Utilities/System   % fail

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%                QualifiedId
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%  Basic structure for naming things

%% The Qualifier's for id's in a spec are established independently
%% from the name of the spec:  all, some, or none might have the
%% name of the spec as their qualifier, and the same qualifier can
%% be used in multiple specs.

type Qualifier = String
type Id        = String

type QualifiedId  = | Qualified Qualifier * Id
type QualifiedIds = List QualifiedId
type Aliases      = QualifiedIds


%% This is the key used in the qualifier maps for UnQualified Id
op UnQualified : Qualifier = "<unqualified>" % a non-parsable id

%% the following are invoked by the parser to make qualified names
op mkUnQualifiedId (id : Id)         : QualifiedId = Qualified (UnQualified, id)
op mkQualifiedId   (q : Id, id : Id) : QualifiedId = Qualified (q,           id)

op unQualifiedId? (id : QualifiedId) : Bool = 
  case id of
    | Qualified(UnQualified, _) -> true
    | _ -> false

op mainId (Qualified (_,main_id) : QualifiedId) : String = main_id

op addQualifier (o_qual: Option Id) (qid as Qualified(q,id): QualifiedId): QualifiedId =
   if q = UnQualified
     then
       case o_qual of
         | None -> qid
         | Some qual -> Qualified(qual,id)
     else qid

%% These are used by translation, morphism code
op unqualified_Bool : QualifiedId = mkUnQualifiedId "Bool"           % used by translate
op Bool_Bool        : QualifiedId = mkQualifiedId ("Bool", "Bool")   % used by translate

op syntactic_qid? (Qualified (q, id)) : Bool =                  % used by translate, morphism
  if q = "Bool" || q = UnQualified then                       % used by translate, morphism
    (case id of
       | "~"   -> true
       | "&&"  -> true  % was "&"
       | "||"  -> true  % was "or"
       | "=>"  -> true
       | "<=>" -> true
       | "="   -> true
       | "~="  -> true
       | _ -> false)
  else
    false

%% This is useful in some error messages, where you want to be very explicit:
op explicitPrintQualifiedId (Qualified (q, id) : QualifiedId) : String =
  if q = UnQualified then
    id
  else
    q ^ "." ^ id

op QualifiedId.show : QualifiedId -> String = printQualifiedId

%% This is useful for most normal messages, where you want to be terse:
op printQualifiedId (Qualified (q, id) : QualifiedId) : String =
  if q = UnQualified then
     id
   else
     printQualifierDotId (q, id)

op printQualifierDotId (q : Qualifier, id : Id) : String =
  if q = "Nat" || q = "String" || q = "Char"    || q = UnQualified then
    id
  else 
    q ^ "." ^ id

%% This is useful when printing names for Lisp, C, Java, etc.:
op printUnderbarQualifiedId (Qualified (q, id) : QualifiedId) : String =
  if q = UnQualified then
    id
  else
    printQualifierUnderbarId (q, id)

op printQualifierUnderbarId (q : Qualifier, id : Id) : String =
  if q = "Nat" || q = "String" || q = "Char" || q = UnQualified then
    id
  else 
    q ^ "_" ^ id

op printAliases (aliases : List QualifiedId) : String =
  case aliases of
    | [] -> fail "printAliases: empty name list"
    | [name] -> printQualifiedId name
    | first::rest ->
      "{" ^ (printQualifiedId first) ^
      (foldl (fn (str, qid) -> str ^ ", " ^ printQualifiedId qid)
             ""
             rest)
      ^ "}"
end-spec