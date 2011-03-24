SortOpInfos qualifying spec

import /Languages/MetaSlang/Specs/StandardSpec

type SortOpInfos = {ops : List OpInfo, sorts : List SortInfo}
op emptyMonoInfo : SortOpInfos = {ops = [], sorts = []}

op isEmptySortOpInfos?: SortOpInfos -> Boolean
def isEmptySortOpInfos? (minfo) =
  minfo.ops = [] && minfo.sorts = []

op addOpInfo2SortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def addOpInfo2SortOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
%  let _ = case opinfo of
%          | (_, _, _, []) -> writeLine ("no definition term!")
%          | _ -> ()
%  in
  case findLeftmost (fn info -> nqid in? info.names) ops of
    | Some _ -> minfo
    | None -> {ops = Cons (opinfo, ops), sorts = minfo.sorts}

op exchangeOpInfoInSortOpInfos: QualifiedId * OpInfo * SortOpInfos -> SortOpInfos
def exchangeOpInfoInSortOpInfos (nqid, opinfo, minfo) =
  let ops = minfo.ops in
  let ops = filter (fn info -> nqid nin? info.names) ops in
  {ops = Cons (opinfo, ops), sorts = minfo.sorts}

op monoInfosContainOp?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainOp? (nqid, minfo) =
  let ops = minfo.ops in
  case findLeftmost (fn info -> nqid in? info.names) ops of
    | Some _ -> true
    | None -> false

op monoInfosContainSort?: QualifiedId * SortOpInfos -> Boolean
def monoInfosContainSort? (nqid, minfo) =
  let srts = minfo.sorts in
  case findLeftmost (fn info -> nqid in? info.names) srts of
    | Some _ -> true
    | None -> false

op addSortInfo2SortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def addSortInfo2SortOpInfos (nqid, sinfo, minfo) =
  if monoInfosContainSort? (nqid, minfo) then 
    minfo 
  else
    {ops   = minfo.ops, 
     sorts = Cons (sinfo, minfo.sorts)}

op exchangeSortInfoInSortOpInfos: QualifiedId * SortInfo * SortOpInfos -> SortOpInfos
def exchangeSortInfoInSortOpInfos (nqid, sinfo, minfo) =
  let sorts = minfo.sorts in
  let sorts = filter (fn info -> nqid nin? info.names) sorts in
  {ops   = minfo.ops, 
   sorts = Cons (sinfo, sorts)}

end-spec
