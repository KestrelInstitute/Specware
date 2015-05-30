G qualifying spec 
(*--------------------------------------------------------------------------------------*)
% symbol                 ::=  simple_name  
%                          |  literal   
%                          |  special_symbol
% simple_name            ::=  first_syllable      { _ next_syllable }*
% first_syllable         ::= first_word_syllable   
%                          |  non_word_syllable
% next_syllable          ::= next_word_syllable    
%                          |  non_word_syllable
% first_word_syllable    ::= word_start_mark     { word_continue_mark }*
% next_word_syllable     ::= word_continue_mark  { word_continue_mark }*
% word_start_mark        ::= letter
% word_continue_mark     ::= letter
%                          | decimal_digit
%                          | ' 
%                          | ?
op WCM'WCM : Nat = 001 (* word_continue_mark *) 
op w00?00m : Nat = 002 (* word_continue_mark *) 
(*--------------------------------------------------------------------------------------*)
% non_word_symbol        ::= non_word_mark       { non_word_mark }*
% non_word_mark          ::= ` ~ ! @ $ ^ & * - = + \ | : < > / ' ?
op `       : Nat = 001                          (* non_word_mark *)(***** ERR?? *****  sjw: fixed grammar *)
op ~       : Nat = 002 (* reserved symbols *)   (* non_word_mark *)(***** ERR?? *****  sjw: fixed documentation *)
op !       : Nat = 003                          (* non_word_mark *)
op @       : Nat = 004                          (* non_word_mark *)
op $       : Nat = 005                          (* non_word_mark *)
op ^       : Nat = 006                          (* non_word_mark *)
op &       : Nat = 007                          (* non_word_mark *)
op *       : Nat = 008                          (* non_word_mark *)
op -       : Nat = 009                          (* non_word_mark *)
% op =     : Nat = 010 (* reserved symbols *)   (* non_word_mark *)
op +       : Nat = 011                          (* non_word_mark *)
op \       : Nat = 012                          (* non_word_mark *)
% op |     : Nat = 013 (* reserved symbols *)   (* non_word_mark *)
% op :     : Nat = 014 (* reserved symbols *)   (* non_word_mark *)
op <       : Nat = 015                          (* non_word_mark *)
op >       : Nat = 016                          (* non_word_mark *)
op /       : Nat = 017                          (* non_word_mark *)
op '       : Nat = 018                          (* non_word_mark *)
op ?       : Nat = 019                          (* non_word_mark *)
op X       : Nat =(` Nat.+
             (G.~ Nat.+ (***** ERR?? *****  sjw: fixed documentation *)
             (! Nat.+
             (@ Nat.+
             ($ Nat.+
             (^ Nat.+
             (& Nat.+
             ( * Nat.+ (*spc rqd*)
             (- Nat.+
            %(= Nat.+
             (+ Nat.+
             (\ Nat.+
            %(| Nat.+
            %(: Nat.+
             (< Nat.+
             (> Nat.+
             (/ Nat.+
             (' Nat.+
              ?)))))))))))))))%)))
op  addY : Nat -> Nat -> Nat -> Nat 
def addY a b c = a + b + c + X
op  Y:Nat = 
    let < : Nat = 20 in 
    let ! : Nat = 40 in 
    let @ : Nat = 60 in 
    (addY < ! @)

op ``      : Nat = 001 (* not reserved ***)     (* non_word_mark *) (***** ERR?? *****  sjw: fixed documentation *)
op ~~      : Nat = 002                          (* non_word_mark *)
op !!      : Nat = 003                          (* non_word_mark *)
op @@      : Nat = 004                          (* non_word_mark *)
op $$      : Nat = 005                          (* non_word_mark *)
op ^^      : Nat = 006                          (* non_word_mark *)
%op &&     : Nat = 007 (* reserved symbols *)   (* non_word_mark *)
op **      : Nat = 008                          (* non_word_mark *)
op --      : Nat = 009                          (* non_word_mark *)
op ==      : Nat = 010 (* reserved symbols *)   (* non_word_mark *)
op ++      : Nat = 011                          (* non_word_mark *)
op \\      : Nat = 012                          (* non_word_mark *)
%op ||     : Nat = 013 (* reserved symbols *)   (* non_word_mark *)
%op ::     : Nat = 014 (* reserved symbols *)   (* non_word_mark *)
%op <<     : Nat = 015                          (* non_word_mark *) (***** ERR?? *****  sjw: fixed documentation *)
op >>      : Nat = 016                          (* non_word_mark *)
op //      : Nat = 017                          (* non_word_mark *)
op ''      : Nat = 018                          (* non_word_mark *)
op ??      : Nat = 019                          (* non_word_mark *)
%op <=>    : Nat = 020 (* reserved symbol *)
%op <-     : Nat = 021 (* reserved symbol *)
%op ~=     : Nat = 022 (* reserved symbol *)
%op =>     : Nat = 023 (* reserved symbol *)
%op ->     : Nat = 024 (* reserved symbol *)
%op +->    : Nat = 025 (* reserved symbol *) 
% special_symbol         ::= _ ( ) [ ] { } ; , .
% 13 ASCII printing characters not allowed as non_word_marks
%         NOTE: There are special symbols plus # % "
%op # : Nat = 0   
%op % : Nat = 0   
%op " : Nat = 0   
%op _ : Nat = 0   (* special_symbol *)   
%op ( : Nat = 0   (* special_symbol *)
%op ) : Nat = 0   (* special_symbol *)
%op [ : Nat = 0   (* special_symbol *)
%op ] : Nat = 0   (* special_symbol *)
%op { : Nat = 0   (* special_symbol *)
%op } : Nat = 0   (* special_symbol *)
%op ; : Nat = 0   (* special_symbol *)
%op , : Nat = 0   (* special_symbol *)
%op . : Nat = 0   (* special_symbol *)
end-spec
