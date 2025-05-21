open itreeTauTheory;
open relationTheory;
open pathTheory;
open arithmeticTheory;
open finite_mapTheory;
open wordsTheory;
open byteTheory;

open pairSyntax;
open sumSyntax;
open listSyntax;

open preamble;
open panPtreeConversionTheory; (* parse_funs_to_ast *)
open panSemTheory; (* eval_def, byte stuff *)
open panLangTheory; (* size_of_shape_def *)
open panItreeSemTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;

local
  val f =
    List.mapPartial
       (fn s => case helperLib.remove_whitespace s of "" => NONE | x => SOME x) o
    String.tokens (fn c => c = #"\n")
in
  fun quote_to_strings q =
    f (Portable.quote_to_string (fn _ => raise General.Bind) q)
  end

fun parse_pancake q =
  let
    val code = quote_to_strings q |> String.concatWith "\n" |> stringSyntax.fromMLstring
  in
    rhs $ concl $ SRULE[] $ EVAL “(parse_funs_to_ast ^code)”
end



val queue' = parse_pancake ‘
fun share_load_net_queue(1 queue_ptr)
{
    var tail = 0;
    var head = 0;
    var capacity = 0;
    var signal = 0;
    !ldw tail, queue_ptr;
    !ldw head, queue_ptr + @biw;
    !ldw capacity, queue_ptr + 2 * @biw;
    !ld8 signal, queue_ptr + 3 * @biw;

    var queue = <tail, head, capacity, signal>;
    return queue;
}
’;

val queue = queue' |> dest_inl |> fst |> dest_cons |> fst
          |> dest_pair |> snd |> dest_pair |> snd |> dest_pair |> snd;

Definition q_def:
  q_sem (s:('a, 'b) bstate) =
  to_stree (mrec_sem (h_prog (^queue, s)))
End

    
Theorem pan_eval_simps[simp]:
    eval s (Const w) = SOME (ValWord w)
  ∧ eval s (Var v) = FLOOKUP s.locals v
  ∧ eval s BaseAddr = SOME (ValWord s.base_addr)
  ∧ eval s (Label fname) = OPTION_IGNORE_BIND (FLOOKUP s.code fname)
                                              (SOME (ValLabel fname))
Proof
  rw[eval_def] >>
  Cases_on ‘FLOOKUP s.code fname’ >> gvs[]
QED

Theorem itree_wbisim_refl[simp] = itree_wbisim_refl;
Theorem apply_update_simp[simp] = cj 1 combinTheory.UPDATE_APPLY;
(* may explode cases if k1 = k2 isn't decidable: luckily we cmp names = strings *)
Theorem do_flookup_simp[simp] = finite_mapTheory.FLOOKUP_UPDATE;
Theorem write_bytearray_0[simp] = cj 1 write_bytearray_def;
Theorem valid_value_simp[simp] = is_valid_value_def;
Theorem shape_of_simp[simp] = shape_of_def;
Theorem h_prog_skip[simp] = cj 1 h_prog_def;

Theorem to_stree_simps[simp] = to_stree_simps;
Theorem mrec_sem_simps[simp] = mrec_sem_simps;
Theorem nb_op_def[simp] = nb_op_def;

Definition addr:
  addr: word64 = 0w
End

Definition bs:
  bs: (64, 'a) bstate =
  <|
    locals := FEMPTY |+ («queue_ptr», ValWord addr);
    sh_memaddrs := {addr; addr + bytes_in_word; addr + 2w * bytes_in_word;
                    byte_align (addr + 3w * bytes_in_word)}
  |>
End

Theorem unwrapping_conditions[simp]:
  (bs: (64, 'a) bstate).locals = FEMPTY |+ («queue_ptr», ValWord addr) ∧
  addr ∈ (bs: (64, 'a) bstate).sh_memaddrs ∧
  addr + bytes_in_word ∈ (bs: (64, 'a) bstate).sh_memaddrs ∧
  addr + 2w * bytes_in_word ∈ (bs: (64, 'a) bstate).sh_memaddrs ∧
  byte_align (addr + 3w * bytes_in_word) ∈ (bs: (64, 'a) bstate).sh_memaddrs
Proof
  rw[bs]
QED
    
        
Theorem unwrapping:
  itree_wbisim
    (q_sem (bs: (64, 'a) bstate))
    (Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes addr F))
         (λx. case x of
              | FFI_return f l =>
     Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + bytes_in_word) F))
         (λx. case x of
              | FFI_return f' l' =>
     Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + 2w * bytes_in_word) F))
         (λx. case x of
              | FFI_return f'' l'' =>
     Vis (FFI_call (SharedMem MappedRead) [1w] (word_to_bytes (addr + 3w * bytes_in_word) F))
         (λx. case x of
              | FFI_return f''' l''' => Ret (SOME (Return (Struct
                                                           [ValWord (word_of_bytes F 0w l);
                                                            ValWord (word_of_bytes F 0w l');
                                                            ValWord (word_of_bytes F 0w l'');
                                                            ValWord (word_of_bytes F 0w l''')])),
                                             (bs: (64, 'a) bstate) with <|locals := FEMPTY; ffi := f'''|>)
              | FFI_final e''' => Ret (SOME (FinalFFI e'''), (bs: (64, 'a) bstate)
                                                             with <|locals := FEMPTY; ffi := f''|>))
              | FFI_final e'' => Ret (SOME (FinalFFI e''), (bs: (64, 'a) bstate)
                                                           with <|locals := FEMPTY; ffi := f'|>))
              | FFI_final e' => Ret (SOME (FinalFFI e'), (bs: (64, 'a) bstate)
                                                         with <|locals := FEMPTY; ffi := f|>))
              | FFI_final e => Ret (SOME (FinalFFI e), (bs: (64, 'a) bstate)
                                                       with locals := FEMPTY)))
Proof
  rw[q_def] >>
  gvs[h_prog_def, h_prog_seq_def, h_prog_dec_def] >>
  gvs[h_prog_sh_mem_load_def] >>
  rw[Once itree_wbisim_cases] >>
  Cases_on ‘r’ >> rw[]
  >- (gvs[h_prog_def, h_prog_seq_def] >> gvs[h_prog_sh_mem_load_def] >>
      rw[panItreeSemTheory.set_var_def, panSemTheory.set_var_def] >>
      simp[eval_def, FLOOKUP_UPDATE] >>
      simp[wordLangTheory.word_op_def, fpOptTheory.option_map_def] >>
      rw[Once itree_wbisim_cases] >>
      Cases_on ‘r’ >> rw[]
      >- (gvs[h_prog_def, h_prog_seq_def] >> gvs[h_prog_sh_mem_load_def] >>
          simp[eval_def] >>
          gvs[pan_op_def, wordLangTheory.word_op_def, fpOptTheory.option_map_def] >>
          rw[Once itree_wbisim_cases] >>
          Cases_on ‘r’ >> rw[]                      
          >- (gvs[h_prog_def, h_prog_seq_def, h_prog_sh_mem_load_def] >>
              rw[panItreeSemTheory.set_var_def, panSemTheory.set_var_def] >>
              simp[eval_def] >>
              gvs[pan_op_def, wordLangTheory.word_op_def, fpOptTheory.option_map_def] >>
              rw[Once itree_wbisim_cases] >>
              Cases_on ‘r’ >> rw[]
              >- (gvs[h_prog_def, h_prog_seq_def, h_prog_dec_def, eval_def] >>                         
                  simp[h_prog_return_def, size_of_shape_def] >>
                  rw[panItreeSemTheory.empty_locals_def, panSemTheory.empty_locals_def] >>
                  gvs[res_var_def])
              >- (rw[panItreeSemTheory.empty_locals_def, panSemTheory.empty_locals_def] >>
                  gvs[res_var_def, Once itree_wbisim_cases]))
          >- (rw[panItreeSemTheory.empty_locals_def, panSemTheory.empty_locals_def] >>
              gvs[res_var_def, Once itree_wbisim_cases]))
      >- (rw[panItreeSemTheory.empty_locals_def, panSemTheory.empty_locals_def] >>
          gvs[res_var_def, Once itree_wbisim_cases]))
  >- (rw[panItreeSemTheory.empty_locals_def, panSemTheory.empty_locals_def] >>
      gvs[res_var_def] >> gvs[Once itree_wbisim_cases])
QED           

Datatype:
  state = start | tail | head | cap | ret
End
   
Inductive trans:
  (∀f l. trans start (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes addr F),
                           FFI_return f l)) tail) ∧
  (∀f. trans start (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes addr F),
                         FFI_final f)) ret) ∧
  (∀f l. trans tail (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + bytes_in_word) F),
                          FFI_return f l)) head) ∧             
  (∀f. trans tail (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + bytes_in_word) F),
                        FFI_final f)) ret) ∧
  (∀f l. trans head (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + 2w * bytes_in_word) F),
                          FFI_return f l)) cap) ∧
  (∀f. trans head (SOME(FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + 2w * bytes_in_word) F),
                        FFI_final f)) ret) ∧
  (∀f l. trans cap (SOME(FFI_call (SharedMem MappedRead) [1w] (word_to_bytes (addr + 3w * bytes_in_word) F),
                         FFI_return f l)) ret) ∧
  (∀f. trans cap (SOME(FFI_call (SharedMem MappedRead) [1w] (word_to_bytes (addr + 3w * bytes_in_word) F),
                       FFI_final f)) ret)
End

CoInductive is_path:
[~vis]
(∀s p e k.
  is_path p (k b) ∧
  trans s (SOME(e, b)) (first p) ⇒
  is_path (pcons s (SOME(e, b)) p) (Vis e k))
[~ret]
(∀r. 
  is_path (stopped_at ret) (Ret r))
[~tau]
(∀p i.
  is_path p i ⇒ is_path p (Tau i))
End

Definition head:
  head x p = (first p = x) 
End

CoInductive always:
  (∀P p. P (stopped_at p) ⇒ G P (stopped_at p)) ∧
  (∀s a P p. (P (pcons s a p) ∧ G P p) ⇒ G P (pcons s a p))
End

Inductive eventually:
  (∀P p. P p ⇒ E P p) ∧
  (∀s a P p. E P p ⇒ E P (pcons s a p))
End

Inductive until:
 (∀P Q p. Q p ⇒ U P Q p) ∧
 (∀P Q s a p. (P (pcons s a p) ∧ U P Q p) ⇒ U P Q (pcons s a p))
End

Definition implication:
  I A B p = (A p ⇒ B p)
End

Definition truth:
  truth p = T
End
    

Definition program:
  pgrm = 
     Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes addr F))
         (λx. case x of
              | FFI_return f l =>
     Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + bytes_in_word) F))
         (λx. case x of
              | FFI_return f' l' =>
     Vis (FFI_call (SharedMem MappedRead) [0w] (word_to_bytes (addr + 2w * bytes_in_word) F))
         (λx. case x of
              | FFI_return f'' l'' =>
     Vis (FFI_call (SharedMem MappedRead) [1w] (word_to_bytes (addr + 3w * bytes_in_word) F))
         (λx. case x of
              | FFI_return f''' l''' => Ret (SOME (Return (Struct
                                                           [ValWord (word_of_bytes F 0w l);
                                                            ValWord (word_of_bytes F 0w l');
                                                            ValWord (word_of_bytes F 0w l'');
                                                            ValWord (word_of_bytes F 0w l''')])),
                                             (bs: (64, 'a) bstate) with <|locals := FEMPTY; ffi := f'''|>)
              | FFI_final e''' => Ret (SOME (FinalFFI e'''), (bs: (64, 'a) bstate)
                                                             with <|locals := FEMPTY; ffi := f''|>))
              | FFI_final e'' => Ret (SOME (FinalFFI e''), (bs: (64, 'a) bstate)
                                                           with <|locals := FEMPTY; ffi := f'|>))
              | FFI_final e' => Ret (SOME (FinalFFI e'), (bs: (64, 'a) bstate)
                                                         with <|locals := FEMPTY; ffi := f|>))
              | FFI_final e => Ret (SOME (FinalFFI e), (bs: (64, 'a) bstate)
                                                       with locals := FEMPTY))
End
    
Theorem program_term:
  is_path p pgrm ⇒ G (I truth (E (head ret))) p
Proof
  rw[] >>
  irule always_coind >>
  rw[implication, truth] >>
  qexists_tac ‘λp. E (head ret) p’ >>
  rw[]
  >- ()            
  >- ()
QED
    
Theorem we_are_live:
  itree_wbisim itree1 itree2 ∧
  (∀p1. is_path p1 itree1 ⇒ G (I A (E B)) p1) ⇒
  (∀p2. is_path p2 itree2 ⇒ G (I A (E B)) p2)
Proof
  
QED
