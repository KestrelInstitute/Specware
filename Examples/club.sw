
Club = spec
  import /Library/DataStructures/Sets

  type Person
  type Club

  axiom Club_ex is ex (c:Club) true
  axiom Person_ex is ex (p:Person) true

  op members (c : Club) : Set Person
  op club_size (c : Club) : Nat = size (members c)

  op add_member (c : Club) (p : Person | ~(p in? (members c))) :
    { c' : Club | members c' = set_insert (p, members c) }

  op remove_member (c : Club) (p : Person | p in? (members c)) :
    { c' : Club | members c' = set_delete (p, members c) }
end-spec


Club1 = transform Club by
{
  maintain (club_size) [lr Set.size_of_insert,
                        lr Set.size_over_set_delete]
}

Club2 = spec
  import Club1
  import /Library/DataStructures/StructuredTypes

  op members_list : Club -> List Person
  def members a = L2S (members_list a)

  theorem members_l2s is
    fa (c) members c = L2S (members_list c)
  proof Isa members_l2s
    by (auto simp add: members_def)
  end-proof
end-spec

Club3 = transform Club2 by {
                        implement (members, members_l2s) [ rl L2S_Cons, rl L2S_delete1 ]
                        }

Club4 = transform Club3 by {
                        finalizeCoType(Club)
                        }
