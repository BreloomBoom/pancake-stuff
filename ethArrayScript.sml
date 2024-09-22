open itreeTauTheory;
open relationTheory;
open pathTheory;
open arithmeticTheory;
open finite_mapTheory;
open wordsTheory;
open byteTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;

Definition weak_tau_def:
  weak_tau m = RTC (λs s'. m s NONE s')
End

Definition weak_trans_def:
  weak_trans m s e s' =
  (∃s'' s'''.
     weak_tau m s s'' ∧
     m s'' (SOME e) s''' ∧
     weak_tau m s''' s')
End

CoInductive safe:
[~ret]
  (∀s r m. safe m s (Ret r))
[~tau]
  (∀s t m. (∀s'. weak_tau m s s' ⇒ safe m s' t) ⇒
   safe m s (Tau t))
[~vis]
  (∀e k s m.
   (∀s'. weak_tau m s s' ⇒ ∃b s''. m s' (SOME(e,b)) s'') ∧ (* not stuck in s *)
   (∀b s'. weak_trans m s (e,b) s' ⇒ safe m s' (k b))      (* all steps valid *)
   ⇒ safe m s (Vis e k))
End

(* Constants *)
    
Definition qCap_def:
  qCap = 512w (* has to be larger than hw q *)
End

Definition free_offset:
  free_off = 9000w
End

Definition active_offset:
  active_off = 19000w
End

Definition hwq_offset:
  hw_off = 29000w
End

(* Datatypes *)
    
Datatype:
  queue = <| hd : word64 ; tl : word64 ; ps : word64 |-> word32 |>
End

(*
  free -> empty -> active -> free
*)
Datatype:
  status = SlotFree | SlotEmpty | SlotActive 
End
    
Datatype:
  ring_desc = <| ptr : word32 ; stat : status |>
End    
  
Datatype:
  state = <| free : queue ; active : queue ; hw_ring : word64 |-> ring_desc |>
End 

(*
  ffi calls
  e.g. FFI_call MappedRead [4w] (word_to_bytes (0w : word64) F)
*)

Datatype:
  ffi_type = free_tail | free_head | free_inc_head
           | active_tail | active_head | active_inc_tail
           | free_read word64 | active_write word64                           
End

Definition lookup_offset:
  lookup_offset type =
    case type of
      free_tail => free_off
    | free_head => free_off + 1w
    | free_inc_head => free_off + 1w
    | active_tail => active_off
    | active_head => active_off + 1w
    | active_inc_tail => active_off
    | free_read i => free_off + 2w + (word_mod i qCap)
    | active_write i => active_off + 2w + (word_mod i qCap)  
End

Datatype:
  ffiname = MappedRead | MappedWrite
End
    
Datatype:
  ffi = FFI_call ffiname (word8 list) (word8 list)
End
    
Definition mread_ffi:
  mread_ffi type =
  FFI_call MappedRead [4w] (word_to_bytes (lookup_offset type) F)
End

Definition mwrite_ffi:
  mwrite_ffi (w : word64) type =
  FFI_call MappedWrite [0w] (word_to_bytes w F ++ word_to_bytes (lookup_offset type) F)
End

Inductive eth:
  (* free queue info *)
  eth s (SOME(mread_ffi free_tail, s.free.tl)) s ∧
  eth s (SOME(mread_ffi free_head, s.free.hd)) s ∧
 
  (* free dequeue *)
  (s.free.tl ≠ s.free.hd ⇒
   eth s (SOME(mread_ffi (free_read s.free.hd), w2w (THE (FLOOKUP s.free.ps s.free.hd)))) s) ∧
  (s.free.tl ≠ s.free.hd ⇒
   eth s (SOME(mwrite_ffi (s.free.hd + 1w) free_inc_head, 0w))
  (s with free := (s.free with hd := s.free.hd + 1w))) ∧
  
  (* free enqueue *)
  (s.free.tl - s.free.hd < qCap ⇒
   eth s NONE (s with free := (s.free with ps := s.free.ps |+ (s.free.tl, w))
                                      with tl := s.free.tl + 1w)) ∧
     
  (* active queue info *)
  eth s (SOME(mread_ffi active_tail, s.active.tl)) s ∧
  eth s (SOME(mread_ffi active_head, s.active.hd)) s ∧

  (* active enqueue *)
  (s.free.tl - s.free.hd < qCap ⇒
   eth s (SOME(mwrite_ffi (w2w w) (active_write s.active.tl), 0w))
  (s with active := (s.active with ps := s.active.ps |+ (s.active.tl, w)))) ∧
  (s.free.tl - s.free.hd < qCap ⇒
   eth s (SOME(mwrite_ffi (s.active.tl + 1w) active_inc_tail, 0w))
  (s with active := (s.active with tl := s.active.tl + 1w))) ∧

  (* active dequeue *)
  (s.active.tl ≠ s.active.hd ⇒
   eth s NONE (s with active := (s.active with hd := s.active.hd + 1w)))
End
