spec

  (* As in LD, we leave names abstract because the logic is parameterized
  over them. In addition, this allows us to refine them in different ways,
  obtaining different instances of the proof checker. *)

  (* We use the library spec for infinite types in order to impose the
  requirement, also present in LD, that there are infinite names. *)

  import translate Libs/Type#Infinite by {X +-> Name}

  (* Unlike LD, we do not set aside particular names for projections, because
  we model product types (vs. record types) explicitly. This also simplifies
  refining names, because there are fewer requirements that their refinement
  must satisfy. *)

endspec
