open bossLib;
open itreeTauTheory;
open relationTheory;
open pathTheory;

val m = Hol_pp.print_apropos;
val f = Hol_pp.print_find;


    
Datatype:
  label = Send | Ready
End

Datatype:
  state = ReadyS | UnreadyS
End

(*
   trans : state -> (label×bool) -> state

   trans : state -> (label×bool) option -> state -> bool
 *)
Inductive trans:
  trans ReadyS (SOME(Send,T)) UnreadyS ∧
  trans UnreadyS NONE ReadyS ∧
  trans UnreadyS (SOME(Ready,F)) UnreadyS ∧
  trans ReadyS (SOME(Ready,T)) ReadyS ∧
  trans ReadyS NONE ReadyS
End

Definition weak_tau_def:
  weak_tau = RTC (λs s'. trans s NONE s')
End

Definition weak_trans_def:
  weak_trans s e s' =
  (∃s'' s'''.
     weak_tau s s'' ∧
     trans s'' (SOME e) s''' ∧
     weak_tau s''' s')
End        

CoInductive safe:
[~ret]
  (∀s r. safe s (Ret r))
[~tau]
  (∀s t. (∀s'. weak_tau s s' ⇒ safe s' t) ⇒
   safe s (Tau t))
[~vis]
  (∀e k s.
   (∀s'. weak_tau s s' ⇒ ∃b s''. trans s' (SOME(e,b)) s'') ∧
   (∀b s'. weak_trans s (e,b) s' ⇒
           safe s' (k b))
   ⇒ safe s (Vis e k))
End

    
Definition rsdriver_def:
  rsdriver =
    itree_unfold (λx. if x then Vis' Send  (λb. F)
                           else Vis' Ready (λb. b)) F
End

Theorem rsdriver:
  rsdriver = Vis Ready (λb. if b then Vis Send (λx. rsdriver)
                                 else rsdriver)
Proof
  rw[rsdriver_def] >>
  ntac 3 $ rw[Once itree_unfold, FUN_EQ_THM]
QED

    
    
Theorem weak_tau1:
  ∀s. (λs s'.
         s = UnreadyS ∧ s' = ReadyS ∨
         s = ReadyS ∧ s' = ReadyS)꙳ ReadyS s
  ⇒ s = ReadyS
Proof
  ntac 2 $ strip_tac >>
  qmatch_asmsub_abbrev_tac ‘R꙳’ >>
  ‘∀x y. x = ReadyS ∧ R꙳ x y ⇒ y = ReadyS’
  by (ho_match_mp_tac RTC_lifts_invariants >> rw[Abbr ‘R’]) >>
  simp[Abbr ‘R’]
QED

Theorem safe_rsdriver1:
  r ∈ {ReadyS; UnreadyS} ⇒ safe r rsdriver
Proof
  strip_tac >>
  irule safe_coind >> 
  qexists ‘λs t. (s = ReadyS ∧ t = rsdriver) ∨
                 (s = UnreadyS ∧ t = rsdriver) ∨
                 (s = ReadyS ∧ t = Vis Send (λx. rsdriver))’ >>
  reverse $ rw[]
  >- gvs[] >>
  pop_assum kall_tac >>
  rpt disj2_tac >> rw[Once rsdriver] >>
  gs[weak_tau_def, weak_trans_def, trans_cases] >>
  simp[weak_tau1] >>
  Cases_on ‘s'’ >> rw[] >>
  qspec_then ‘UnreadyS’ mp_tac weak_tau1 >> fs[]
QED

Theorem safe_rsdriver:
  safe r rsdriver
Proof
  Cases_on ‘r’ >> simp[safe_rsdriver1]
QED


CoInductive is_path:
[~tau]
(∀s s' p i.
  is_path (pcons s' a p) i ∧
  trans s NONE s' ⇒
  is_path (pcons s NONE (pcons s' a p)) i)
[~action]
(∀s s' p e k.
  is_path (pcons s' a p) (k b) ∧
  trans s (SOME(e, b)) s' ⇒
  is_path (pcons s (SOME(e, b)) (pcons s' a p)) (Vis e k))
End

Definition head:
  head x p = (first p = x) 
End

Definition action:
  action s a s' p = (first p = s ∧ first_label p = a ∧ first (tail p) = s')
End

CoInductive always:
  (P (pcons s a p) ∧ G P p) ⇒ G P (pcons s a p)
End

Inductive eventually:
  (∀P p. P p ⇒ E P p) ∧
  (∀s a P p. E P p ⇒ E P (pcons s a p))
End

Definition implication:
  I A B p = (A p ⇒ B p)
End    
    
CoInductive perp_enabled:
  ∀Tr p s s' a b c d. perp_enabled Tr (pcons c d p) ∧
                      (s, a, s') ∈ Tr ∧ trans s b c ⇒
                      perp_enabled Tr (pcons s b (pcons c d p))
End

Definition occurs:
  occurs Tr p = ∃s a s'. (s, a, s') ∈ Tr ∧ E (action s a s') p
End
  
Definition fairness:
  fair Tr p = G (I (perp_enabled Tr) (occurs Tr)) p
End


Theorem path_inf:
  ∀i. (is_path p i ⇒ ~(finite p))
Proof
  Induct_on ‘finite p’ using finite_path_ind >>
  rw[] >> rw[Once is_path_cases] >> simp[]
QED                                  
    
Theorem infinite_pcons:
  ~(finite p) ⇒ (∃a b c. p = pcons a b c)
Proof
  spose_not_then assume_tac >> rw[] >>
  ‘is_stopped p’ by (Cases_on ‘p’ using path_cases >> fs[]) >>
  gvs[finite_thm, is_stopped_def] 
QED

Theorem infinite_pcons1:
  ~(finite p) ∧ head ReadyS p ⇒ (∃b c d e. p = pcons ReadyS b (pcons c d e))
Proof
 rw[] >>
 ‘∃x y z. p = pcons x y z’ by (metis_tac[infinite_pcons]) >> fs[] >>
 ‘∃r s t. z = pcons r s t’ by (metis_tac[infinite_pcons]) >> fs[head]
QED

Theorem is_path_rsdriver_cases:
  (is_path (pcons a b' c) (rsdriver:(bool,label,'a) itree) ∨
   is_path (pcons a b' c) ((Vis Send (λb. rsdriver)):(bool,label,'a) itree)) ⇒
  (is_path c (rsdriver:(bool,label,'a) itree) ∨
   is_path c ((Vis Send (λb. rsdriver)):(bool,label,'a) itree))
Proof
  rw[] >>
  qhdtm_x_assum `is_path` mp_tac >>
  rw[Once is_path_cases] >> simp[] >>
  pop_assum kall_tac >>
  gvs[Once rsdriver] >>                     
  Cases_on ‘b’ >> fs[]
QED

Theorem fair_pcons:
  fair {(ReadyS,SOME (Send,T),UnreadyS)} (pcons a b' c) ⇒
  fair {(ReadyS,SOME (Send,T),UnreadyS)} c
Proof
  rw[Once always_cases, fairness]
QED
    
Theorem not_UnreadyS:
  (is_path (pcons a b c) (rsdriver:(bool,label,'a) itree) ∨
   is_path (pcons a b c) ((Vis Send (λx. rsdriver)):(bool,label,'a) itree)) ∧
  head ReadyS (pcons a b c) ∧
  ¬E (action ReadyS (SOME(Send, T)) UnreadyS) (pcons a b c) ⇒
  perp_enabled {(ReadyS, SOME(Send, T), UnreadyS)} (pcons a b c)
Proof
  rw[] >>
  irule perp_enabled_coind >>
  qexists_tac ‘λs t. s = {(ReadyS, SOME(Send, T), UnreadyS)} ∧
                     head ReadyS t ∧
                     ¬E (action ReadyS (SOME(Send, T)) UnreadyS) t ∧
                     (is_path t (rsdriver:(bool,label,'a) itree) ∨
                      is_path t ((Vis Send (λx. rsdriver)):(bool,label,'a) itree))’ >>
  rw[] >>
  ntac 3 $ pop_last_assum kall_tac >>
  ‘∃p q r s. a1 = pcons ReadyS p (pcons q r s)’ by (metis_tac[path_inf, infinite_pcons1]) >>
  gvs[head] >>
  irule_at Any is_path_rsdriver_cases >> qexistsl_tac [‘p’, ‘ReadyS’] >> simp[] >>
  fs[Once eventually_cases, Once is_path_cases] >>
  gvs[trans_cases, action]
QED

Theorem live_rsdriver:
  is_path p rsdriver ∧ fair {(ReadyS, SOME(Send, T), UnreadyS)} p ⇒
  G (I (head ReadyS) (E (action ReadyS (SOME(Send, T)) UnreadyS))) p 
Proof
  rw[] >>
  irule always_coind >>
  qexists_tac ‘{ p | (is_path p (rsdriver:(bool,label,'a) itree) ∨
                      is_path p ((Vis Send (λb. rsdriver)):(bool,label,'a) itree)) ∧
                     fair {(ReadyS, SOME(Send, T), UnreadyS)} p }’ >> rw[] >>
  ntac 2 (pop_last_assum kall_tac) >>
  ‘∃a b c. a0 = pcons a b c’ by (metis_tac[path_inf, infinite_pcons]) >>
  fs[implication] >>
  irule_at Any is_path_rsdriver_cases >> qexistsl_tac [‘b’, ‘a’] >> simp[] >>
  irule_at Any fair_pcons >> qexistsl_tac [‘b’, ‘a’] >> simp[] >>
  rw[] >> fs[fairness] >>
  Cases_on ‘perp_enabled {(ReadyS, SOME(Send, T), UnreadyS)} (pcons a b c)’
  >- (gvs[Once always_cases, implication, occurs] >> rw[])
  >- (metis_tac[not_UnreadyS])
  >- (gvs[Once always_cases, implication, occurs] >> rw[])
  >- (metis_tac[not_UnreadyS])
QED

