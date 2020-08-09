Require Import Basics.
Require Import Types.
Require Import HProp.
Require Import Diagrams.Diagram.
Require Import Diagrams.Sequence.
Require Import Diagrams.Cocone.
Require Import Colimits.Sequential.
Require Import Colimits.Colimit.
Require Import Colimits.Colimit_Sigma.
Require Import Spaces.Nat.
Require Import Spaces.Finite.
Require Import Types.Universe.
Require Import HoTT.TruncType HoTT.DProp.

Local Open Scope path_scope.

(** A proof that polynomial functors with finite fibres
    preserve sequential colimits. Work in progress. *)

(** We begin by showing that sequential colimits commute
    with products, i.e. that
    
      Colimit A * Colimit B = Colimit (i |-> A i * B i) 
  *)

Section Preservation_of_Products.

  Context `{Univalence} {A B : Sequence}.

  Let f n := @arr _ A n _ 1.
  Let g n := @arr _ B n _ 1.

  (* The sequence whose ith component is the type A_i x B_i *)

  Definition times (C D : Sequence) : Sequence.
  Proof.
    pose (h n := @arr _ C n _ 1); pose (k n := @arr _ D n _ 1);
    srapply Build_Sequence.
    - exact (fun i => C i * D i).
    - exact (fun i => functor_prod (h i) (k i)).
  Defined.

  (* The constant fibred sequence constB(i;x) = B(i) *)
  Definition constB : FibSequence A
  := Build_FibSequence A (fun x => B x.1) (fun x => g x.1).

  (* Some natural number tomfoolery. *)
  Local Definition R k i
    := nat_plus_n_Sm k i : (k + i).+1 = (k + i.+1)%nat.

  Local Lemma RCoh {n m} (p : n = m) z
    : (coe (ap B p) z)^+ = coe (ap B (ap S p)) (z^+).
  Proof. induction p; exact 1. Defined.

  Local Definition KCoh {X Y} {x1 x2 : X} {y} F G (p : x1 = x2) :
    G x2 (coe (ap Y p) y) = coe (ap Y (ap F p)) (G x1 y).
  Proof. destruct p; reflexivity. Defined.

  Local Lemma RPlus k i x
    : (coe (ap B (R k i)^) x)^+ = coe (ap B (R k.+1 i)^) x^+.
  Proof.
     srapply (KCoh S g (R k i)^
      @ ap10 (ap coe (ap (ap B) (ap_V S (nat_plus_n_Sm k i)))) x^+).
  Defined.

  (* An equivalence C(k, n, a) -> B(k+n). *)

  Definition F x k
    : fib_seq_to_seq constB x k <~> B (k+x.1)%nat.
  Proof.
    srapply Build_Equiv.
    + revert x; induction k as [|k h]; intro x.
      - exact idmap.
      - exact (coe (ap B (R k x.1)^) o h x^++).
    + revert x; induction k as [| k h]; intro x.
      - srapply isequiv_idmap.
      - srapply isequiv_compose.
  Defined.

  Local Lemma up_F x k y
    : (F x k y)^+ = F x k.+1 y^+.
  Proof. 
    revert y; revert x; induction k as [| k h]; intros x y.
    + exact 1.
    + srapply (RPlus _ _ _ @ ap (coe _) (h (x^++) y)).
  Defined.

  (* At each fiber, the sequentialised constant B sequence is
     just the shifted sequence. *)
  Definition equiv_const_fib_shifted (x : sig A)
    : Colimit (fib_seq_to_seq constB x) -> Colimit (shift_seq B x.1).
  Proof.
    srapply functor_colimit; srapply Build_diagram_equiv.
    - srapply Build_DiagramMap.
      * intro i. srapply F.
      * intros k j p; destruct p. srapply up_F.
    - intro i. srapply equiv_isequiv.
  Defined.

  Lemma equiv_const_fib_shifted_beta (x : sig A) k y
    : ap (equiv_const_fib_shifted x) (glue (fib_seq_to_seq constB x) k y)
      = ap (inj (shift_seq B x.1) k.+1) (up_F x k y)^
         @ glue (shift_seq B x.1) k (F x k y).
  Proof. srapply Colimit_rec_beta_colimp. Defined.

  Definition isequiv_const_fib_shifted (x : sig A)
    : IsEquiv (equiv_const_fib_shifted x).
  Proof. srapply isequiv_functor_colimit. Defined.

  Definition equiv_const_fib (x : sig A)
    : Colimit (fib_seq_to_seq constB x) -> Colimit B
  := colim_shift_seq_to_colim_seq B x.1 o equiv_const_fib_shifted x.

  Theorem isequiv_const_fib (x : sig A)
    : IsEquiv (equiv_const_fib x).
  Proof. srapply isequiv_compose. Defined.

  Definition transport_forall_constant_codomain
    {X Y : Type} {C : X -> Type}
    {x1 x2 : X} (p : x1 = x2) (h : C x1 -> Y)
    : transport (fun x : X => C x -> Y) p h
      == (fun y => h (transport _ p^ y)).
  Proof. induction p; intro x; exact 1. Defined.

  Definition assocB k
    : Colimit (shift_seq B k.+1) <~> Colimit (succ_seq (shift_seq B k)).
  Proof.
    srapply equiv_functor_colimit; srapply Build_diagram_equiv.
    - srapply Build_DiagramMap.
      + intros i. simpl. srapply (coe (ap B (R i k)^)).
      + intros i j p x; induction p. srapply (RPlus _ _ _).
    - intros i. simpl. srapply (isequiv_transport idmap _).
  Defined.

  Definition assocB_beta k i x
    : ap (assocB k) (glue (shift_seq B k.+1) i x)
      = ap (inj (succ_seq (shift_seq B k)) i.+1) (RPlus i k x)^
        @ glue (succ_seq (shift_seq B k)) i (coe (ap B (R i k)^) x).
  Proof. srapply Colimit_rec_beta_colimp. Defined.

  Definition assocB_ap_inj {i k} {x y} {p : x = y}
    : ap (assocB k) (ap (inj _ i) p)
      = ap (inj (succ_seq (shift_seq B k)) i) (ap (coe (ap B (R i k)^)) p).
  Proof.
    destruct p; exact 1.
  Defined.

  Lemma inj_nat_coe {n m x} (p : n = m)
    : inj B m (coe (ap B p) x) = inj B n x.
  Proof. induction p; exact 1. Defined.

  Local Definition J {X Y Z} {x1 x2 : X} {y} {I : forall x, Y x -> Z} (p : x1 = x2)
    : I x2 (coe (ap Y p) y) = I x1 y.
  Proof. destruct p; reflexivity. Defined.

  (* 
     I = inj B
     G = (-)^
     Q i x = glue _ i x
     F = succ
    p^ = R k i : (i + k.+1) = (i + k).+1.
                         x2 = x1
   *)

  Local Lemma L {X Y Z} {x1 x2 : X} {y} {F G} {I : forall x, Y x -> Z} {p : x1 = x2}
  (Q : forall x y, I (F x) (G x y) = I x y)
    : (ap (I (F x1)) (KCoh F G p^ @
          ap10 (ap coe (ap (ap Y) (ap_V F p))) (G x2 y))^
      @ Q x1 (coe (ap Y p^) y)) @ J p^
        = J (ap F p)^ @ Q x2 y.
  Proof. induction p. simpl. rewrite concat_1p, concat_p1. exact 1. Defined.
   
  Theorem equiv_of_equivs1 k
    : colim_shift_seq_to_colim_seq B k 
        o colim_succ_seq_to_colim_seq (shift_seq B k) o assocB k
      == colim_shift_seq_to_colim_seq B (k.+1).
  Proof.
    srapply seq_colimit_uniq.
    - intros i x. simpl. srapply (J (R i k)^).
    - intros i x. rewrite ap_compose, ap_compose.
      rewrite assocB_beta. rewrite ap_pp.
      rewrite colim_succ_seq_to_colim_seq_ap_inj.
      rewrite (colim_succ_seq_to_colim_seq_beta_glue (shift_seq B k)).
      rewrite ap_pp. rewrite colim_shift_seq_to_colim_seq_ap_inj.
      rewrite colim_shift_seq_to_colim_seq_beta_glue.
      rewrite colim_shift_seq_to_colim_seq_beta_glue. 
      unfold RPlus. srapply (L (glue _)).
  Defined.

  Theorem equiv_of_equivs2 i x
    : equiv_const_fib_shifted (i;x) 
        o colim_succ_seq_to_colim_seq (fib_seq_to_seq constB (i;x))
      == colim_succ_seq_to_colim_seq (shift_seq B i) o assocB i
         o equiv_const_fib_shifted (i.+1; x^+).
  Proof.
    srapply seq_colimit_uniq.
    - intros j y. exact 1.
    - intros j y.
      rewrite ap_compose. rewrite concat_p1, concat_1p.
      (* simplifying the LHS *)
      rewrite colim_succ_seq_to_colim_seq_beta_glue.
      rewrite equiv_const_fib_shifted_beta.
      (* simplifying the RHS *)
      rewrite (ap_compose _ (colim_succ_seq_to_colim_seq _)).
      rewrite (ap_compose _ (assocB i)).
      rewrite equiv_const_fib_shifted_beta.
      rewrite ap_pp, assocB_ap_inj.
      rewrite ap_pp, colim_succ_seq_to_colim_seq_ap_inj.
      rewrite assocB_beta.
      rewrite ap_pp, colim_succ_seq_to_colim_seq_ap_inj.
      rewrite (colim_succ_seq_to_colim_seq_beta_glue (shift_seq B _) _). 
      rewrite concat_p_pp.
      rewrite <- (ap_pp (inj (shift_seq B i) j.+2)).
      srapply whiskerR.
      srapply (ap (fun q => ap (inj _ j.+2) q) _).
      rewrite (ap_V (coe (ap B (R j.+1 i)^))).
      srapply moveL_pV. srapply moveR_Vp. srapply moveL_pV.
      exact 1.
  Defined.

  Theorem constB_fiber (a : Colimit A)
    : fib_seq_to_type_fam constB a -> Colimit B.
  Proof.
    revert a; srapply Colimit_ind.
    - intros i x. srapply equiv_const_fib.
    - intros i j p x; destruct p.
      srapply moveR_transport_p.
      srapply path_forall; intro y.
      srapply (_@(transport_forall_constant_codomain
                (glue A i x)^
                (equiv_const_fib (i;x)) y)^).
      rewrite inv_V. rewrite transport_idmap_ap.
      rewrite fib_seq_to_type_fam_beta_glue.
      unfold equiv_const_fib.
      rewrite (equiv_of_equivs2 i x y).
      rewrite (equiv_of_equivs1 i _).
      exact 1.
  Defined.

  Theorem isequiv_constB_fiber a : IsEquiv (constB_fiber a).
  Proof.
    admit.
  Admitted.
  
  Definition equiv_constB_fiber a
    : fib_seq_to_type_fam constB a <~> Colimit B
  := Build_Equiv _  _ _ (isequiv_constB_fiber a).

  Theorem alex1
    : Colimit A * Colimit B <~> sig (fib_seq_to_type_fam constB).
  Proof.
    transitivity {_ : Colimit A & Colimit B}.
    - make_equiv.
    - srapply equiv_functor_sigma.
      + exact idmap.
      + srapply isequiv_idmap.
      + intro a. simpl. srapply equiv_path. symmetry.
        srapply path_universe_uncurried. srapply equiv_constB_fiber.
      + intro a. srapply isequiv_path.
  Defined.

  Theorem alex2
    : Colimit (sig_seq constB) <~> Colimit (times A B).
    srapply equiv_functor_colimit; srapply Build_diagram_equiv.
    - srapply Build_DiagramMap.
      + simpl. intros i [x y]. exact (x, y).
      + intros i j p x; induction p. exact 1.
    - intro i. simpl.
      srapply (equiv_sigma_prod0 (A i) (B i)).(equiv_isequiv).
  Defined.

  Definition seqcolim_corollary
    : Colimit (sig_seq constB) <~> sig (fib_seq_to_type_fam constB).
  Proof.
    srapply equiv_seq_colim_sum_to_sum_seq_colim.
  Defined.

  Definition equiv_colimTimes_timesColim 
    : Colimit A * Colimit B <~> Colimit (times A B)
  := alex2 oE seqcolim_corollary^-1 oE alex1.

End Preservation_of_Products.


(* Data for a polynomial functor *)

Record Polynomial := {
  label : Type;
  arity : label -> nat
}.

Section Presentations_of_Unit.

  Context `{Univalence}.

  (* A bit of a warmup. *)

  Definition equiv_unit_fin0 {X} : Unit <~> (Fin 0 -> X).
  Proof. srapply equiv_empty_rec. Defined.
  
  Definition equiv_unit_fin1 {X} : X <~> (Fin 1 -> X).
  Proof.
    srapply (equiv_compose' _ (equiv_unit_rec X)).
    srapply equiv_functor_forall'.
    - unfold Fin. srapply (sum_empty_l Unit).
    - intros b. simpl. srapply equiv_idmap.
  Defined.

  Definition equiv_fin_prod {n X} : (Fin n.+1 -> X) <~> (Fin n -> X) * X.
  Proof.
    srapply equiv_inverse. srapply equiv_compose'.
    + exact ((Fin n -> X) * (Unit -> X)).
    + srapply equiv_sum_distributive.
    + srapply equiv_functor_prod'.
      - exact equiv_idmap.
      - srapply equiv_unit_rec.
  Defined.

  Definition equiv_fin_prod_2 {X} : (Fin 2 -> X) <~> X * X.
  Proof.
    srapply (equiv_compose' _ equiv_fin_prod).
    srapply equiv_functor_prod'.
    - srapply (equiv_inverse equiv_unit_fin1).
    - exact equiv_idmap.
  Defined.

  (* The constant sequence on an object along with a
     proof that Colimit (sequence_const Unit) <~> Unit. *)

  Definition sequence_const (D : Type) : Sequence.
  Proof.
    srapply Build_Sequence.
    - exact (fun _ => D).
    - exact (fun _ x => x).
  Defined.

  Lemma equal_one_everywhere (i : nat) (x : Unit)
    : inj (sequence_const Unit) i x = inj (sequence_const Unit) 0 tt.
  Proof.
    induction x. induction i.
    + exact 1.
    + exact (glue (sequence_const Unit) i tt @ IHi).
  Defined.

  Lemma contr_sequence_unit : Contr (Colimit (sequence_const Unit)).
  Proof.
    srapply Build_Contr.
    + exact (inj (sequence_const Unit) 0 tt).
    + srapply Colimit_ind.
      - intros i z. symmetry. srapply equal_one_everywhere.
      - intros i j Q x. induction Q. simpl.
        srapply (transport_paths_r _ _ @ _).
        srapply moveR_Vp. 
        srapply moveL_pV.
        induction x. exact 1.
  Defined.

  Theorem equiv_constUnit_Unit 
    : Colimit (sequence_const Unit) <~> Unit.
  Proof.
    srapply equiv_adjointify.
    - srapply Colimit_rec. srapply Build_Cocone.
      + intros i x. exact tt.
      + intros i j Q x; induction Q. exact 1.
    - intro x. exact (inj (sequence_const Unit) 0 x).
    - simpl. intro x. induction x. exact 1.
    - simpl. intro x. srapply path_contr.
  Defined.

End Presentations_of_Unit.


Section Preservation_of_Finite_Exponents.

  Context `{Univalence} {A : Sequence}.

  Local Definition f n := @arr _ A n _ 1.

  (* The sequence whose ith component is the type [n] -> A_i. *)

  Definition sequence_finlim (n : nat) : Sequence
  := Build_Sequence (fun i => Fin n -> A i) (fun i h => f i o h).

  (* A proof that Colimit (sequence_finlim 0) <~> Unit. *)

  Lemma equiv_fin0_unit {X} : (Fin 0 -> X) <~> Unit.
  Proof. srapply Build_Equiv. exact (fun _ => tt). Defined.

  Lemma diagram_equiv_finlim0_constUnit 
    : sequence_finlim 0 ~d~ sequence_const Unit.
  Proof.
    srapply equiv_sequence.
    - simpl. exact equiv_fin0_unit.
    - intros n E. srapply (_;_).
      * srapply Build_Equiv; exact (fun _ => tt).
      * intros x. simpl. symmetry. srapply eta_unit.
  Defined.

  Lemma equiv_colim_finlim0_constUnit 
    : Colimit (sequence_finlim 0) <~> Colimit (sequence_const Unit).
  Proof.
    srapply equiv_functor_colimit; srapply diagram_equiv_finlim0_constUnit.
  Defined.

  Lemma equiv_colim_finlim0_unit : Colimit (sequence_finlim 0) <~> Unit.
  Proof.
    srapply (equiv_compose' equiv_constUnit_Unit _).
    srapply equiv_colim_finlim0_constUnit.
  Defined.

  Lemma equiv_n_diagrams {n}
   : times (sequence_finlim n) A ~d~ sequence_finlim n.+1.
  Proof.
    srapply Build_diagram_equiv.
    - srapply Build_DiagramMap.
      + simpl. intro i. exact (equiv_inverse equiv_fin_prod).
      + intros i j Q x. induction Q. srapply path_forall. intro k. induction k.
        * simpl. reflexivity.
        * simpl. induction b. reflexivity.
    - simpl. intro i. exact (equiv_inverse equiv_fin_prod).(equiv_isequiv).
  Defined.

  Lemma equiv_n_colimits {n}
    : Colimit (times (sequence_finlim n) A) <~> Colimit (sequence_finlim n.+1).
  Proof.
    srapply (equiv_functor_colimit equiv_n_diagrams).
  Defined.

  Theorem equiv_commute_finprod_seqcolim (n : nat)
    : Colimit (sequence_finlim n) <~> (Fin n -> Colimit A).
  Proof.
    induction n as [|n h].
    + srapply (_ oE equiv_colim_finlim0_unit). exact equiv_unit_fin0.
    + srapply (_ oE equiv_n_colimits^-1).
      srapply (_ oE equiv_colimTimes_timesColim^-1).
      srapply (equiv_fin_prod^-1 oE _).
      srapply (equiv_functor_prod' h equiv_idmap). 
  Defined.

End Preservation_of_Finite_Exponents.

Section Preservation_of_Sigma.

  Context `{Funext} {P : Polynomial} {A : Type} {C : A -> Sequence}.

  Let Label := P.(label).
  Let B := P.(arity).

  (* The sequence i |-> Σ(x : A) (C x i) *)
  Definition sequence_sigma : Sequence.
  Proof.
    srapply Build_Diagram.
    - exact (fun i => {a : A & C a i}).
    - simpl. intros i j g x.
      exact (x.1 ; C x.1 _f g x.2).
  Defined.

  Lemma iscolimit_sequence_sigma
    : IsColimit sequence_sigma (sig (fun a => Colimit (C a))).
  Proof.
    srapply iscolimit_sigma.
  Defined.

  (* A proof that Colim(i |-> Σ(x : A) (C x i)) <~> Σ(x : A) Colim(C x i).
     Follows directly from the results in the Colimit library. *)

  Theorem  equiv_sigma_colim 
    : sig (fun a => Colimit (C a)) <~> Colimit sequence_sigma.
  Proof.
    srapply (colimit_unicity iscolimit_sequence_sigma).
  Defined.

End Preservation_of_Sigma.


Section Poly_Functors_Preserve_SeqColimits.

  (* The main result: polynomial functors preserve sequential colimits. *)

  Context `{Univalence}.

  Definition poly_functor_obj (P : Polynomial) : Type -> Type.
    intro X. exact (sigT (fun a => Fin (P.(arity)(a)) -> X)).
  Defined.

  Definition poly_functor_mor {A B : Type} (P : Polynomial)
      : (A -> B) -> (poly_functor_obj P A -> poly_functor_obj P B).
  Proof.
    intros f x. destruct x as [a h]. exact (a ; fun y => f (h y)).
  Defined.

  Definition apply_poly_sequence (P : Polynomial) (A : Sequence)
    : Sequence.
  Proof.
    srapply (sequence_sigma (A := P.(label))).
    + exact (fun a => sequence_finlim (A := A) (P.(arity)(a))).
  Defined.

  Definition equiv_poly_fibre (A : Sequence) (P : Polynomial) (a : P.(label))
      : Colimit (sequence_finlim (A := A) (P.(arity) a))
        <~> (Fin (P.(arity) a) -> Colimit A).
  Proof.
    srapply equiv_commute_finprod_seqcolim.
  Defined.

  Theorem poly_preserves_seqcolim (P : Polynomial) (A : Sequence)
    : poly_functor_obj P (Colimit A) <~> Colimit (apply_poly_sequence P A).
  Proof.
    pose (f n := @arr _ A n _ 1).
    unfold apply_poly_sequence.
    unfold poly_functor_obj. 
    srapply equiv_compose'.
    + exact {A0 : label P & Colimit (sequence_finlim (A := A) (arity P A0))}.
    + srapply equiv_sigma_colim.
    + srapply equiv_functor_sigma'.
      * srapply equiv_idmap.
      * intro a. simpl. srapply equiv_inverse. srapply equiv_poly_fibre.
  Defined.

End Poly_Functors_Preserve_SeqColimits.