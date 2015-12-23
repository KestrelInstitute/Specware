(* Copyright 2015 Kestrel Institute. See file LICENSE for license details *)

TypeOpInfos qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec

type TypeOpInfos = {ops : List OpInfo, types : List TypeInfo}
op emptyMonoInfo : TypeOpInfos = {ops = [], types = []}

op isEmptyTypeOpInfos?: TypeOpInfos -> Bool
def isEmptyTypeOpInfos? (minfo) =
  minfo.ops = [] && minfo.types = []

op addOpInfo2TypeOpInfos: QualifiedId * OpInfo * TypeOpInfos -> TypeOpInfos
def addOpInfo2TypeOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
%  let _ = case opinfo of
%          | (_, _, _, []) -> writeLine ("no definition term!")
%          | _ -> ()
%  in
  case findLeftmost (fn info -> nqid in? info.names) ops of
    | Some _ -> minfo
    | None -> {ops = Cons (opinfo, ops), types = minfo.types}

op exchangeOpInfoInTypeOpInfos: QualifiedId * OpInfo * TypeOpInfos -> TypeOpInfos
def exchangeOpInfoInTypeOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
  let ops = filter (fn info -> nqid nin? info.names) ops in
  {ops = Cons (opinfo, ops), types = minfo.types}

op monoInfosContainOp?: QualifiedId * TypeOpInfos -> Bool
def monoInfosContainOp? (nqid, minfo) =
  let ops = minfo.ops in
  case findLeftmost (fn info -> nqid in? info.names) ops of
    | Some _ -> true
    | None -> false

op monoInfosContainType?: QualifiedId * TypeOpInfos -> Bool
def monoInfosContainType? (nqid, minfo) =
  let srts = minfo.types in
  case findLeftmost (fn info -> nqid in? info.names) srts of
    | Some _ -> true
    | None -> false

op addTypeInfo2TypeOpInfos: QualifiedId * TypeInfo * TypeOpInfos -> TypeOpInfos
def addTypeInfo2TypeOpInfos (nqid, sinfo, minfo) =
  if monoInfosContainType? (nqid, minfo) then 
    minfo 
  else
    {ops   = minfo.ops, 
     types = Cons (sinfo, minfo.types)}

op exchangeTypeInfoInTypeOpInfos: QualifiedId * TypeInfo * TypeOpInfos -> TypeOpInfos
def exchangeTypeInfoInTypeOpInfos (nqid, sinfo, minfo) =
  let types = minfo.types in
  let types = filter (fn info -> nqid nin? info.names) types in
  {ops   = minfo.ops, 
   types = Cons (sinfo, types)}

end-spec
