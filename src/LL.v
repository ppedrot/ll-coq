Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Classes.Equivalence.
Require Import AAC.

Parameter var : Type.

Hypothesis var_eq_dec : forall x y : var, {x = y} + {x <> y}.

Inductive φ :=
| φ_pos : var -> φ
| φ_neg : var -> φ
| φ_one : φ
| φ_bot : φ
| φ_top : φ
| φ_nul : φ
| φ_tns : φ -> φ -> φ
| φ_par : φ -> φ -> φ
| φ_wth : φ -> φ -> φ
| φ_pls : φ -> φ -> φ
| φ_bng : φ -> φ
| φ_whn : φ -> φ.

Fixpoint dual_φ (A : φ) :=
match A with
| φ_pos x => φ_neg x
| φ_neg x => φ_pos x
| φ_one => φ_bot
| φ_bot => φ_one
| φ_top => φ_nul
| φ_nul => φ_top
| φ_tns A B => φ_par (dual_φ A) (dual_φ B)
| φ_par A B => φ_tns (dual_φ A) (dual_φ B)
| φ_wth A B => φ_pls (dual_φ A) (dual_φ B)
| φ_pls A B => φ_wth (dual_φ A) (dual_φ B)
| φ_bng A => φ_whn (dual_φ A)
| φ_whn A => φ_bng (dual_φ A)
end.

Notation "P °" := (dual_φ P) (at level 1, left associativity, format "P °").

Notation "1" := (φ_one).
Notation "⊥" := (φ_bot).
Notation "⊤" := (φ_top).
Notation "0" := (φ_nul).

Notation "A ⊗ B" := (φ_tns A B) (at level 40).
Notation "A ⅋ B" := (φ_par A B) (at level 40).
Notation "A ⊕ B" := (φ_pls A B) (at level 50).
Notation "A & B" := (φ_wth A B) (at level 50).
Notation "! A" := (φ_bng A) (at level 10, format "!  A").
Notation "? A" := (φ_whn A) (at level 10, format "?  A").

Definition φ_eq_dec : forall A B : φ, {A = B} + {A <> B}.
Proof.
intros A B; decide equality; apply var_eq_dec.
Defined.

Definition sequent := list φ.

(* Definition permutation (Γ Δ : sequent) := forall (P : φ),
  count_occ φ_eq_dec Γ P = count_occ φ_eq_dec Δ P. *)

Definition permutation (Γ Δ : sequent) := Sorting.Permutation.Permutation Γ Δ.

Inductive derivation : sequent -> Prop :=
| drv_axm : forall A,
  derivation (A :: A° :: nil)
| drv_cut : forall Γ Δ A,
  derivation (A :: Γ) -> derivation (A° :: Δ) -> derivation (Γ ++ Δ)
| drv_prm : forall Γ Δ,
  permutation Γ Δ -> derivation Γ -> derivation Δ
| drv_one :
  derivation (1 :: nil)
| drv_bot : forall Γ,
  derivation Γ -> derivation (⊥ :: Γ)
| drv_top : forall Γ,
  derivation (⊤ :: Γ)
| drv_tns : forall Γ Δ A B,
  derivation (A :: Γ) -> derivation (B :: Δ) -> derivation (A ⊗ B :: Γ ++ Δ)
| drv_par : forall Γ A B,
  derivation (A :: B :: Γ) -> derivation (A ⅋ B :: Γ)
| drv_wth : forall Γ A B,
  derivation (A :: Γ) -> derivation (B :: Γ) -> derivation (A & B :: Γ)
| drv_pls_1 : forall Γ A B,
  derivation (A :: Γ) -> derivation (A ⊕ B :: Γ)
| drv_pls_2 : forall Γ A B,
  derivation (B :: Γ) -> derivation (A ⊕ B :: Γ)
| drv_drl : forall Γ A,
  derivation (A :: Γ) -> derivation (? A :: Γ)
| drv_wkn : forall Γ A,
  derivation Γ -> derivation (? A :: Γ)
| drv_ctr : forall Γ A,
  derivation (? A :: ? A :: Γ) -> derivation (? A :: Γ)
| drv_bng : forall Γ A,
  derivation (A :: List.map φ_whn Γ) -> derivation (! A :: List.map φ_whn Γ)
.

Ltac cauto := auto with typeclass_instances.

Section Permutation.

Import Sorting.Permutation.

(* Lemma permutation_nil : forall Γ, permutation nil Γ -> Γ = nil.
Proof.
intros Γ; induction Γ as [|A Γ]; [reflexivity|].
unfold permutation; intros Hperm; specialize (Hperm A); simpl in Hperm.
destruct φ_eq_dec; now intuition.
Qed.

Lemma permutation_cons : forall Γ Δ A, permutation (A :: Γ) Δ ->
  { Δs | Δ = (fst Δs) ++ A :: (snd Δs) /\ permutation Γ ((fst Δs) ++ (snd Δs)) }.
Proof.
intros Γ; induction Γ as [|B Γ]; intros Δ A Hperm.
  exists (nil, nil); simpl; split; [|unfold permutation; now auto].
  destruct Δ as [|B Δ].
    specialize (Hperm A); simpl in Hperm; destruct φ_eq_dec; exfalso; congruence.
    destruct (φ_eq_dec A B) as [Heq|Hdf]; subst; [f_equal|exfalso].
      admit.
      specialize (Hperm B).
      rewrite (@count_occ_cons_neq _ _ _ A B) in Hperm; [|congruence].
      now simpl in Hperm; destruct φ_eq_dec; congruence.
SearchAbout list.
Locate Permutation.
Print Sorting.Permutation. *)

Lemma permutation_ind : forall (P : sequent -> sequent -> Prop),
  (P nil nil) ->
  (forall Γ Δ1 Δ2 A, permutation Γ (Δ1 ++ Δ2) ->
    P Γ (Δ1 ++ Δ2) -> P (A :: Γ) (Δ1 ++ A :: Δ2)) ->
  forall Γ Δ, permutation Γ Δ -> P Γ Δ.
Proof.
intros P Hnil Hcons; induction Γ as [|A Γ]; intros Δ Hperm.
  apply Sorting.Permutation.Permutation_nil in Hperm; subst; apply Hnil.
  assert (HIn : In A Δ) by (apply (@Permutation_in _ (A :: Γ)); simpl; tauto).
  apply in_split in HIn; destruct HIn as [Δ1 [Δ2 HΔ]]; rewrite HΔ in *.
  assert (Hperm' : permutation Γ (Δ1 ++ Δ2)) by (eapply Permutation_cons_app_inv; eassumption).
  now apply Hcons; [|apply IHΓ]; assumption.
Qed.

End Permutation.

Section Phase_semantics.

Class Monoid := {
  M : Type;
  M_eq : M -> M -> Prop;
  Equivalence_M_eq :> Equivalence M_eq;
  M_op : M -> M -> M;
  M_nul : M;
  Associative_M_op :> Associative M_eq M_op;
  Commutative_M_op :> Commutative M_eq M_op;
  Unit_M_op :> Unit M_eq M_op M_nul;
  Proper_M_op :> Proper (M_eq ==> M_eq ==> M_eq) M_op
}.

Coercion M : Monoid >-> Sortclass.

Notation "x · y" := (M_op x y) (at level 40).

Section Definitions.

Context {M : Monoid}.

Ltac mreplace s t :=
  let H := fresh "H" in
  assert (H : M_eq s t); [|rewrite H; clear H].

Class fact := {
  fact_set : M -> Prop;
  fact_compat :> Proper (M_eq ==> iff) fact_set
}.

Coercion fact_set : fact >-> Funclass.

Definition fact_eq (X Y : fact) := forall x, X x <-> Y x.

Global Instance Equivalence_fact_eq {M : Monoid} : Equivalence fact_eq.
Proof.
split; unfold fact_eq.
  intros X x; now auto.
  intros X Y x; now auto.
  intros X Y Z H1 H2 x; now firstorder.
Qed.

Class assignation := assignation_fun : var -> fact.
Context {assign : assignation}.

Class pole := pole_set : fact.
Context {pole : pole}.

Global Instance Proper_fact_set : Proper (fact_eq ==> M_eq ==> iff) (@fact_set).
Proof.
intros X Y HXY x y Hxy; simpl.
split; intros H; apply HXY; first [rewrite Hxy|rewrite <- Hxy]; assumption.
Qed.

Global Program Instance orth (X : fact) : fact :=
  { fact_set := (fun x => forall y, X y -> pole (x · y)) }.
Next Obligation.
apply proper_sym_impl_iff; [cauto|].
intros x y H HR z Hz.
mreplace (y · z) (x · z); [rewrite H; reflexivity|now eauto].
Qed.

Notation "X ⌝" := (orth X) (at level 1, left associativity, format "X ⌝").

Lemma orth_closed : forall X, fact_eq X⌝⌝⌝ X⌝.
Proof.
intros X x; split; unfold orth; simpl.
  intros Hx y Hy; apply Hx; intros z Hz.
  mreplace (y · z) (z · y); [aac_reflexivity|].
  now apply Hz; assumption.
  intros Hx y Hy.
  mreplace (x · y) (y · x); [aac_reflexivity|].
  apply Hy; now intuition.
Qed.

Lemma orth_incl : forall (X : fact) x, X x -> X⌝⌝ x.
Proof.
intros X x Hx; unfold orth; simpl; intros y Hy.
mreplace (x · y) (y · x); [aac_reflexivity|].
now apply Hy; assumption.
Qed.

Global Instance Proper_orth : Proper (fact_eq ==> fact_eq) orth.
Proof.
intros X Y Heq x; split; unfold orth; simpl; intros H; firstorder.
Qed.

(* Program Instance fact_dsj (X Y : fact) : fact :=
  { fact_set := fun x => X x \/ Y x }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq H; rewrite <- Heq; intuition.
Qed. *)

Inductive fact_prd_set (X Y : fact) (z : M) : Prop :=
| fact_prd_set_intro :
  forall x y, X x -> Y y -> M_eq z (x · y) -> fact_prd_set X Y z.

Global Program Instance fact_prd (X Y : fact) : fact :=
  { fact_set := fact_prd_set X Y }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq [z w Hz Hw H]; exists z w; solve [auto|rewrite <- Heq; assumption].
Qed.

Notation "X ⊙ Y" := (fact_prd X Y) (at level 40).

Global Instance Proper_fact_prd : Proper (fact_eq ==> fact_eq ==> fact_eq) fact_prd.
Proof.
intros X1 X2 HeqX Y1 Y2 HeqY z; split; intros [x y Hx Hy H]; exists x y;
  first [apply HeqX|apply HeqY|idtac]; assumption.
Qed.

Global Program Instance fact_dsj (X Y : fact) : fact :=
  { fact_set := fun x => X x \/ Y x }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq H; rewrite <- Heq; now intuition.
Qed.

Notation "X ∪ Y" := (fact_dsj X Y) (at level 50).

Global Instance Proper_fact_dsj : Proper (fact_eq ==> fact_eq ==> fact_eq) fact_dsj.
Proof.
intros X1 X2 HeqX Y1 Y2 HeqY x; split; intros [Hl|Hr]; simpl; solve [
  left; apply HeqX; assumption|
  right; apply HeqY; assumption].
Qed.

Global Program Instance fact_one : fact := { fact_set := fun x => M_eq x M_nul }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq H; rewrite <- Heq; now auto.
Qed.

Global Program Instance fact_nul : fact := { fact_set := fun x => False }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq; intuition.
Qed.

Record fact_bng_set (X : fact) (x : M) : Prop := {
  fact_bng_fct : X x;
  fact_bng_one : fact_one⌝⌝ x;
  fact_bng_dup : M_eq (x · x) x
}.

Global Program Instance fact_bng (X : fact) : fact :=
  { fact_set := fact_bng_set X }.
Next Obligation.
apply proper_sym_impl_iff; [now cauto|].
intros x y Heq [Hx H1 Hd]; split; rewrite <- Heq; assumption.
Qed.

Global Instance Proper_fact_bng : Proper (fact_eq ==> fact_eq) fact_bng.
Proof.
intros X1 X2 HeqX x; split; intros [Hx H1 Hd]; split;
first [rewrite HeqX|rewrite <- HeqX|idtac]; assumption.
Qed.

Fixpoint eval_φ A : fact :=
match A with
| φ_pos x => (assign x)⌝⌝
| φ_neg x => (assign x)⌝
| 1 => fact_one⌝⌝
| ⊥ => fact_one⌝
| ⊤ => fact_nul⌝
| 0 => fact_nul⌝⌝
| A ⊗ B => (fact_prd (eval_φ A) (eval_φ B))⌝⌝
| A ⅋ B => (fact_prd (eval_φ A)⌝ (eval_φ B)⌝)⌝
| A & B => (fact_dsj (eval_φ A)⌝ (eval_φ B)⌝)⌝
| A ⊕ B => (fact_dsj (eval_φ A) (eval_φ B))⌝⌝
| ! A => (fact_bng (eval_φ A))⌝⌝
| ? A => (fact_bng (eval_φ A)⌝)⌝
end.

Fixpoint sequent_to_φ Γ :=
match Γ with
| nil => ⊥
| A :: Γ => A ⅋ (sequent_to_φ Γ)
end.

Lemma fact_prd_comm : forall X Y, fact_eq (fact_prd X Y) (fact_prd Y X).
Proof.
intros X Y z; split; intros [x y Hx Hy H]; exists y x;
solve [assumption|rewrite Commutative_M_op; assumption].
Qed.

Lemma fact_prd_assoc : forall X Y Z, fact_eq (fact_prd X (fact_prd Y Z)) (fact_prd (fact_prd X Y) Z).
Proof.
intros X Y Z w; split.
  intros [x ? Hx [y z Hy Hz H'] H].
  exists (x · y) z; [exists x y| |]; first [assumption|reflexivity|idtac].
  rewrite H, H'; aac_reflexivity.
  intros [? z [x y Hx Hy H] Hz H'].
  exists x (y · z); [|exists y z|]; first [assumption|reflexivity|idtac].
  rewrite H', H; aac_reflexivity.
Qed.

Lemma fact_prd_closed_l : forall X Y, fact_eq Y⌝⌝ Y ->
  fact_eq (fact_prd X⌝⌝ Y)⌝ (fact_prd X Y)⌝.
Proof.
intros X Y Heq w; split; intros H; simpl in *.
  intros z [x y Hx Hy Hz].
  now apply H; exists x y; [apply orth_incl| |]; assumption.
  intros z [x y Hx Hy Hz]; rewrite Hz.
  mreplace (w · (x · y)) (x · (w · y)); [aac_reflexivity|].
  apply Hx; clear x Hx Hz; intros x Hx.
  mreplace ((w · y) · x) (w · (x · y)); [aac_reflexivity|].
  apply H; exists x y; solve [assumption|reflexivity].
Qed.

Lemma fact_prd_closed_r : forall X Y, fact_eq X⌝⌝ X ->
  fact_eq (fact_prd X Y⌝⌝)⌝ (fact_prd X Y)⌝.
Proof.
intros X Y Hrw.
rewrite fact_prd_comm.
rewrite fact_prd_closed_l; [|assumption].
rewrite fact_prd_comm; reflexivity.
Qed.

(* Lemma fact_prd_dual : forall X, fact_eq (fact_prd X X⌝) pole.
Proof.
intros X z; split; intros H.
  destruct H as [x y Hx Hy Hz]; rewrite Hz.
  rewrite Commutative_M_op; apply Hy; assumption.
*)

End Definitions.

(* Redefinition of notations because Coq does not accept Global Notation... *)

Notation "X ⌝" := (orth X) (at level 1, left associativity, format "X ⌝").
Notation "X ⊙ Y" := (fact_prd X Y) (at level 40).
Notation "X ∪ Y" := (fact_dsj X Y) (at level 50).

Section Soundness.

Context {M : Monoid}.
Context {assign : assignation}.
Context {pole : pole}.

Ltac mreplace s t :=
  let H := fresh "H" in
  assert (H : M_eq s t); [|rewrite H; clear H].

Lemma eval_φ_dual_aux : forall A, fact_eq (eval_φ A°) (eval_φ A)⌝ /\ fact_eq (eval_φ A)⌝⌝ (eval_φ A).
Proof.
intros A; induction A; simpl; split;
  first [reflexivity|symmetry; apply orth_closed|now apply orth_closed|idtac].
  destruct IHA1 as [IHA1_l IHA1_r]; destruct IHA2 as [IHA2_l IHA2_r];
  rewrite orth_closed, IHA1_l, IHA2_l, IHA1_r, IHA2_r; reflexivity.
  destruct IHA1 as [IHA1_l IHA1_r]; destruct IHA2 as [IHA2_l IHA2_r];
  rewrite IHA1_l, IHA2_l; reflexivity.
  destruct IHA1 as [IHA1_l IHA1_r]; destruct IHA2 as [IHA2_l IHA2_r];
  rewrite IHA1_l, IHA2_l; reflexivity.
  destruct IHA1 as [IHA1_l IHA1_r]; destruct IHA2 as [IHA2_l IHA2_r];
  rewrite orth_closed, IHA1_l, IHA2_l, IHA1_r, IHA2_r; reflexivity.
  destruct IHA as [IHA_l IHA_r];
  rewrite orth_closed, IHA_l, IHA_r; reflexivity.
  destruct IHA as [IHA_l IHA_r];
  rewrite IHA_l; reflexivity.
Qed.

Lemma eval_φ_dual_compat : forall A, fact_eq (eval_φ A°) (eval_φ A)⌝.
Proof.
apply eval_φ_dual_aux.
Qed.

Lemma eval_φ_dual_closed : forall A, fact_eq (eval_φ A)⌝⌝ (eval_φ A).
Proof.
apply eval_φ_dual_aux.
Qed.

Notation "[[ Γ ]]" := (eval_φ (sequent_to_φ Γ)) (format "[[ Γ ]]").

(* Definition eval_sequent Γ : fact := eval_φ (sequent_to_φ Γ). *)

Lemma eval_sequent_app_compat : forall Γ Δ,
  fact_eq [[Γ ++ Δ]] (fact_prd [[Γ]]⌝ [[Δ]]⌝)⌝.
Proof.
intros Γ; induction Γ as [|A Γ]; intros Δ; simpl.
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  set (X := eval_φ (sequent_to_φ Δ)).
  assert (HX : fact_eq X⌝⌝ X) by (apply eval_φ_dual_closed); clearbody X.
  intros x; split; intros Hx.
    intros ? [u xc Hu Hxc H]; rewrite H, Hu; clear H Hu.
    mreplace (x · (M_nul · xc)) (xc · x); [aac_reflexivity|].
    now apply Hxc; assumption.
    now rewrite <- HX; intros xc Hxc; apply Hx; exists M_nul xc; simpl; solve [aac_reflexivity|assumption].
  rewrite IHΓ.
  rewrite fact_prd_closed_r; [|now apply orth_closed].
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  rewrite fact_prd_assoc; reflexivity.
Qed.

Lemma eval_sequent_permutation_compat : forall Γ Δ,
  permutation Γ Δ -> fact_eq [[Γ]] [[Δ]].
Proof.
apply permutation_ind; simpl.
  reflexivity.
  intros Γ Δ1 Δ2 A Hperm IH; rewrite IH.
  do 2 rewrite eval_sequent_app_compat; simpl.
  repeat (rewrite fact_prd_closed_r; [|now apply orth_closed]).
  rewrite <- fact_prd_comm with (Y := (eval_φ A)⌝).
  rewrite <- fact_prd_assoc.
  rewrite fact_prd_comm with (Y := (eval_φ A)⌝).
  now reflexivity.
Qed.

Ltac simpl_sequent :=
  simpl sequent_to_φ in *; unfold eval_φ in *; simpl eval_φ in *; fold eval_φ in *.

Lemma eval_φ_sound_axm : forall A, [[A :: A° :: nil]] M_nul.
Proof.
intros A; simpl_sequent.
rewrite eval_φ_dual_compat.
rewrite fact_prd_closed_r with (Y := fact_one); [|now apply orth_closed].
rewrite fact_prd_closed_r; [|now apply orth_closed].
rewrite fact_prd_assoc, eval_φ_dual_closed.
intros ? [z k Hz Hk H]; rewrite H; clear H; simpl in Hk; rewrite Hk; clear k Hk.
mreplace (M_nul · (z · M_nul)) z; [aac_reflexivity|].
destruct Hz as [xc x Hxc Hx H]; rewrite H; clear H.
now apply Hxc; assumption.
Qed.

Lemma eval_φ_sound_cut : forall Γ Δ A,
  [[A :: Γ]] M_nul -> [[A° :: Δ]] M_nul -> [[Γ ++ Δ]] M_nul.
Proof.
intros Γ Δ A IHHΓ1 IHHΓ2; simpl_sequent.
rewrite eval_sequent_app_compat.
intros p [x y Hx Hy H]; rewrite H; clear p H.
mreplace (M_nul · (x · y)) (y · x); [aac_reflexivity|].
rewrite <- orth_closed in Hy; apply Hy.
intros yc Hyc.
mreplace (x · yc) (M_nul · (x · yc)); [aac_reflexivity|].
apply IHHΓ2; exists x yc; first [reflexivity|assumption|idtac].
rewrite eval_φ_dual_compat; intros xc Hxc.
mreplace (x · xc) (M_nul · (xc · x)); [aac_reflexivity|].
now apply IHHΓ1; exists xc x; solve [reflexivity|assumption].
Qed.

Lemma eval_φ_sound_prm : forall Γ Δ,
  [[Γ]] M_nul -> permutation Γ Δ -> [[Δ]] M_nul.
Proof.
intros Γ Δ IHHΓ Hperm.
now rewrite <- (eval_sequent_permutation_compat Γ Δ); assumption.
Qed.

Lemma eval_φ_sound_one : [[1 :: nil]] M_nul.
Proof.
simpl_sequent.
rewrite fact_prd_closed_l; [|now apply orth_closed].
rewrite fact_prd_closed_r; [|now apply orth_closed].
intros z [x y Hx Hy H]; rewrite H; clear H.
mreplace (M_nul · (x · y)) (x · y); [aac_reflexivity|].
now apply Hx; assumption.
Qed.

Lemma eval_φ_sound_tns : forall Γ Δ A B,
  [[A :: Γ]] M_nul -> [[B :: Δ]] M_nul -> [[A ⊗ B :: Γ ++ Δ]] M_nul.
Proof.
intros Γ Δ A B IHHΓ1 IHHΓ2; simpl_sequent.
rewrite fact_prd_closed_l; [|now apply orth_closed].
rewrite eval_sequent_app_compat.
rewrite fact_prd_closed_r; [|now apply orth_closed].
intros z [x y Hx Hy H]; rewrite H; clear z H.
destruct Hy as [u v Hu Hv H]; rewrite H; clear y H.
mreplace (M_nul · (x · (u · v))) (x · (u · v)); [aac_reflexivity|].
apply Hx; exists u v; first [reflexivity|rewrite <- eval_φ_dual_closed].
  clear x Hx; intros x Hx.
  mreplace (u · x) (M_nul · (x · u)); [aac_reflexivity|].
  now apply IHHΓ1; exists x u; solve [assumption|reflexivity].
  clear x Hx; intros y Hy.
  mreplace (v · y) (M_nul · (y · v)); [aac_reflexivity|].
  now apply IHHΓ2; exists y v; solve [assumption|reflexivity].
Qed.

Lemma eval_φ_sound_bng : forall Γ A, [[A :: map φ_whn Γ]] M_nul -> [[! A :: map φ_whn Γ]] M_nul.
Proof.
intros Γ A HΓ; simpl_sequent.
rewrite fact_prd_closed_l; [|now apply orth_closed].
intros w [x y Hx Hy H]; rewrite H; clear w H.
mreplace (M_nul · (x · y)) (y · (M_nul · x)); [aac_reflexivity|].
apply Hy; clear y Hy; revert A x Hx HΓ.
induction Γ as [|B Γ]; intros A x Hx HΓ; simpl_sequent.
  intros z Hz; rewrite Hz; clear z Hz.
  mreplace ((M_nul · x) · M_nul) (x · M_nul); [aac_reflexivity|].
  apply Hx; split; [|apply orth_incl; simpl; reflexivity|aac_reflexivity].
  rewrite <- eval_φ_dual_closed; intros z Hz; apply HΓ.
  now exists z M_nul; [assumption|apply orth_incl; simpl; reflexivity|aac_reflexivity].

  rewrite fact_prd_closed_l in HΓ; [|now apply orth_closed].
  rewrite fact_prd_closed_r in HΓ; [|now apply orth_closed].
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [u v Hu Hv H]; rewrite H; clear w H.
  mreplace ((M_nul · x) · (u · v)) (v · (M_nul · (x · u))); [aac_reflexivity|].
  rewrite fact_prd_assoc in HΓ.
  apply Hv; apply (IHΓ (A ⅋ ? B)); unfold eval_φ in *; fold eval_φ in *;
  (rewrite fact_prd_closed_r; [|now apply orth_closed]).
    clear v Γ IHΓ HΓ Hv; intros z [Hz Hz1 Hzd]; destruct Hu as [Hu Hu1 Hud].
    mreplace ((x · u) · z) (x · (z · u)); [aac_reflexivity|].
    apply Hx; split.
      rewrite <- eval_φ_dual_closed; intros k Hk.
      mreplace ((z · u) · k) (z · (k · u)); [aac_reflexivity|].
      now apply Hz; exists k u; [assumption|split; assumption|aac_reflexivity].
      intros k Hk.
      mreplace ((z · u) · k) (z · (k · u)); [aac_reflexivity|].
      apply Hz1; intros c Hc; rewrite Hc; clear c Hc.
      mreplace ((k · u) · M_nul) (u · k); [aac_reflexivity|].
      now apply Hu1; assumption.
      mreplace ((z · u) · (z · u)) ((z · z) · (u · u)); [aac_reflexivity|].
      now rewrite Hzd, Hud; reflexivity.
    rewrite fact_prd_closed_l; [|now apply orth_closed].
    now assumption.
Qed.

Theorem eval_φ_sound : forall Γ, derivation Γ -> [[Γ]] M_nul.
Proof.
intros Γ HΓ; induction HΓ; simpl_sequent.
  (* axiom *)
  now apply eval_φ_sound_axm.
  (* cut *)
  now apply (eval_φ_sound_cut _ _ A); assumption.
  (* permutation *)
  now apply (eval_φ_sound_prm Γ Δ); assumption.
  (* 1 *)
  now apply eval_φ_sound_one.
  (* ⊥ *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros z [x y Hx Hy H]; rewrite H, Hx; clear H Hx.
  mreplace (M_nul · (M_nul · y)) (y · M_nul); [aac_reflexivity|].
  now apply Hy; assumption.
  (* ⊤ *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  now intros z [x y Hx Hy H]; rewrite H; clear H; now inversion Hx.
  (* ⊗ *)
  now apply eval_φ_sound_tns; assumption.
  (* ⅋ *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  rewrite fact_prd_closed_r in IHHΓ; [|now apply orth_closed].
  now rewrite <- fact_prd_assoc; assumption.
  (* & *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [z x Hz Hx H]; rewrite H; clear w H; destruct Hz as [Hz|Hz].
    apply IHHΓ1; exists z x; solve [assumption|reflexivity].
    apply IHHΓ2; exists z x; solve [assumption|reflexivity].
  (* ⊕_1 *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [z x Hz Hx H]; rewrite H; clear w H; apply IHHΓ.
  exists z x; [|assumption|reflexivity].
  now intros u Hu; apply Hz; simpl; tauto.
  (* ⊕_2 *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [z x Hz Hx H]; rewrite H; clear w H; apply IHHΓ.
  exists z x; [|assumption|reflexivity].
  now intros u Hu; apply Hz; simpl; tauto.
  (* dereliction *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [x y Hx Hy H]; rewrite H; clear w H; apply IHHΓ.
  exists x y; [|assumption|reflexivity].
  now destruct Hx as [Hx _ _]; assumption.
  (* weakening *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [x y Hx Hy H]; rewrite H; clear w H; destruct Hx as [_ Hx _].
  mreplace (M_nul · (x · y)) (x · (M_nul · y)); [aac_reflexivity|].
  apply Hx; intros z Hz; rewrite Hz; clear z Hz.
  mreplace ((M_nul ·y) · M_nul) (y · M_nul); [aac_reflexivity|].
  now apply Hy; assumption.
  (* contraction *)
  rewrite fact_prd_closed_l; [|now apply orth_closed].
  intros w [x y Hx Hy H]; rewrite H; clear w H.
  assert (Hd := fact_bng_dup _ _ Hx); rewrite <- Hd; apply IHHΓ.
  exists x (x · y); [apply orth_incl; assumption|apply orth_incl|aac_reflexivity].
  now exists x y; [apply orth_incl; assumption|assumption|aac_reflexivity].
  (* promotion *)
  apply eval_φ_sound_bng; assumption.
Qed.

End Soundness.

(* Section Witness.

(* We need a formula A such that neither A nor A° is provable. *)

Existing Instance eq_equivalence.

Program Let XOR_Monoid : Monoid := {|
  M := bool;
  M_eq := @eq bool;
  M_op := xorb;
  M_nul := false
|}.
Next Obligation.
intros x y z; symmetry; apply Bool.xorb_assoc.
Qed.
Next Obligation.
intros x y; apply Bool.xorb_comm.
Qed.
Next Obligation.
split.
  apply Bool.xorb_false_r.
  apply Bool.xorb_false_l.
Qed.
Next Obligation.
repeat intro; congruence.
Qed.

Program Let T : @fact XOR_Monoid := {| fact_set := fun x => x = true |}.
Program Let T_pole : pole := T.

Program Let α : assignation := fun (_ : var) => T.

Lemma no_derivation_one_par_one : ~ derivation (1 ⅋ 1 :: nil).
Proof.
intros Hd; apply (@eval_φ_sound XOR_Monoid α T_pole) in Hd.
specialize (Hd false); unfold eval_φ in Hd; fold eval_φ in Hd; discriminate Hd.
repeat rewrite orth_closed.
exists false false; try reflexivity; apply orth_incl; [|reflexivity].
exists true true; first [reflexivity|simpl]; intros ? ?; subst; reflexivity.
Qed.

Program Let O_pole : pole := fact_nul.

Lemma no_derivation_bot_tns_bot : ~ derivation (⊥ ⊗ ⊥ :: nil).
Proof.
intros Hd; apply (@eval_φ_sound XOR_Monoid α O_pole) in Hd.
specialize (Hd false); unfold eval_φ in Hd; fold eval_φ in Hd; elim Hd.
repeat rewrite orth_closed.
exists false false; [|apply orth_incl; reflexivity|reflexivity].
intros b [x y Hx Hy H]; rewrite H; clear b H.
elim (Hx false); reflexivity.
Qed.

End Witness. *)

Section Completeness.

Inductive syntactic_rel : sequent -> sequent -> Prop :=
| synrel_prm : forall Γ Δ, permutation Γ Δ -> syntactic_rel Γ Δ
| synrel_ctr : forall Γ A, syntactic_rel (? A :: ? A :: Γ) (? A :: Γ).

Definition syntactic_eq := clos_refl_sym_trans _ syntactic_rel.

Instance Reflexive_syntactic_eq : Reflexive syntactic_eq.
Proof.
intros Γ; apply rst_refl.
Qed.

Instance Symmetric_syntactic_eq : Symmetric syntactic_eq.
Proof.
intros Γ Δ H; apply rst_sym; assumption.
Qed.

Instance Transitive_syntactic_eq : Transitive syntactic_eq.
Proof.
intros Γ Δ Ξ Hl Hr; eapply rst_trans; eassumption.
Qed.

Instance Equivalence_syntactic_eq : Equivalence syntactic_eq.

Lemma permutation_syntactic_eq_incl : forall Γ Δ, permutation Γ Δ -> syntactic_eq Γ Δ.
Proof.
intros Γ Δ H.
apply rst_step; apply synrel_prm; assumption.
Qed.

Lemma Proper_syntactic_eq_permutation : Proper (permutation ==> permutation ==> iff) syntactic_eq.
Proof.
intros Γ1 Γ2 HΓ Δ1 Δ2 HΔ.
apply permutation_syntactic_eq_incl in HΓ.
apply permutation_syntactic_eq_incl in HΔ.
split; intros; rewrite HΓ, HΔ in *; tauto.
Qed.

Instance Proper_syntactic_eq_app : Proper (syntactic_eq ==> syntactic_eq ==> syntactic_eq) (@app φ).
Proof.
intros Γ1 Γ2 HΓ Δ1 Δ2 HΔ; revert Δ1 Δ2 HΔ.
apply clos_rst_rst1n in HΓ.
induction HΓ as [Γ|Γ1 Γ2 Γ3]; intros Δ1 Δ2 HΔ.
  apply clos_rst_rst1n in HΔ.
  induction HΔ as [Δ|Δ1 Δ2 Δ3].
    now reflexivity.
    transitivity (Γ ++ Δ2); [|assumption].
    refine (let P := _ in or_ind (P Γ Δ1 Δ2) (_ (P Γ Δ2 Δ1)) H); [|now intuition].
    clear; intros Γ Δ1 Δ2 HΔ; induction HΔ as [Δ1 Δ2|Δ].
      now apply rst_step, synrel_prm, Permutation.Permutation_app_head.
      transitivity (? A :: ? A :: Δ ++ Γ).
        now apply rst_step, synrel_prm, Permutation.Permutation_app_comm.
      transitivity (? A :: Δ ++ Γ).
        now apply rst_step, synrel_ctr.
        now apply rst_step, synrel_prm; apply (Permutation.Permutation_app_comm (? A :: Δ) Γ).
  transitivity (Γ2 ++ Δ1); [clear - H|apply IHHΓ; eassumption].
  refine (let P := _ in or_ind (P Γ1 Γ2 Δ1) (_ (P Γ2 Γ1 Δ1)) H); [|now intuition].
  clear; intros Γ1 Γ2 Δ HΓ; induction HΓ as [Γ1 Γ2|Γ].
    now apply rst_step, synrel_prm, Permutation.Permutation_app_tail.
    now simpl; apply rst_step, synrel_ctr.
Qed.

Program Instance Syntactic_Monoid : Monoid := {
  M := sequent;
  M_op := @app _;
  M_eq := syntactic_eq;
  M_nul := nil
}.
Next Obligation.
intros Γ Δ Ξ; rewrite app_assoc; reflexivity.
Qed.
Next Obligation.
intros Γ Δ; apply permutation_syntactic_eq_incl.
apply Permutation.Permutation_app_comm; apply Permutation.Permutation_refl.
Qed.
Next Obligation.
split; intros Γ.
  rewrite app_nil_l; reflexivity.
  rewrite app_nil_r; reflexivity.
Qed.
Next Obligation.
apply Proper_syntactic_eq_app.
Qed.

Instance Proper_syntactic_eq_derivation : Proper (syntactic_eq ==> iff) derivation.
Proof.
apply proper_sym_impl_iff; [change (Symmetric (@M_eq Syntactic_Monoid)); cauto|].
intros Γ Δ Heq HΓ; apply clos_rst_rst1n in Heq.
induction Heq as [Γ|Γ Δ Ξ]; [assumption|apply IHHeq].
clear - H HΓ; destruct H as [H|H]; induction H as [Γ Δ|Γ].
  now eapply drv_prm; eassumption.
  now apply drv_ctr; assumption.
  now eapply drv_prm; [apply Permutation.Permutation_sym|]; eassumption.
  now apply drv_wkn; assumption.
Qed.

Program Instance provable_pole : fact := {
  fact_set := fun Γ => derivation Γ
}.
Next Obligation.
apply Proper_syntactic_eq_derivation.
Qed.

Program Let pole : pole := provable_pole.

Program Let fact_cst (v : var) : fact := {| fact_set := fun Γ => syntactic_eq Γ (φ_pos v :: nil) |}.
Next Obligation.
apply proper_sym_impl_iff; [change (Symmetric (@M_eq Syntactic_Monoid)); cauto|].
intros Γ1 Γ2 HΓ Hrw; rewrite <- Hrw; symmetry; assumption.
Qed.

Program Let α : assignation := fun v : var => (fact_cst v)⌝.

Lemma syntactic_eq_cons_app : forall A Γ, syntactic_eq (A :: Γ) (Γ ++ A :: nil).
Proof.
intros A Γ; apply rst_step, synrel_prm.
replace (A :: Γ) with ((A :: nil) ++ Γ) by reflexivity.
now apply Permutation.Permutation_app_comm.
Qed.

Lemma syntactic_eq_idempotent : forall Γ,
  syntactic_eq (Γ · Γ) Γ -> {Δ | Γ = map φ_whn Δ}.
Proof.
intros Γ Heq.
assert (Hc : {Δ | Γ = map φ_whn Δ} + {exists A, In A Γ /\ forall B, A <> ? B}).
  clear; induction Γ as [|A Γ].
    left; exists nil; reflexivity.
    destruct IHΓ as [[Δ HΔ]|H]; [|now right; destruct H as [B HB]; exists B; intuition].
    assert (Heq : {B | A = ? B} + {forall B, A <> ? B}).
      now destruct A; intuition (eauto||congruence).
    destruct Heq as [[B HB]|Hr].
      now left; exists (B :: Δ); simpl; congruence.
      now right; exists A; intuition.
destruct Hc as [?|Hc]; [assumption|exfalso].
assert (Hcount :
  forall Γ Δ A, syntactic_eq Γ Δ -> (forall B, A <> ? B) ->
  count_occ φ_eq_dec Γ A = count_occ φ_eq_dec Δ A).
  clear; intros Γ Δ A Heq HA.
  apply clos_rst_rst1n in Heq; induction Heq as [Γ|Γ1 Γ2 Γ3].
    reflexivity.
    etransitivity; [|eassumption].
    refine (let P := _ in or_ind (P Γ1 Γ2) (_ (P Γ2 Γ1)) H); [|now intuition].
    clear - HA; intros Γ1 Γ2 Hr; induction Hr.
      now induction H; simpl; repeat destruct φ_eq_dec; congruence.
      unfold count_occ.
      destruct (φ_eq_dec); [exfalso; intuition congruence|reflexivity].
destruct Hc as [A [Hi HA]].
assert (H := Hcount _ _ A Heq HA); clear - H Hi.
assert (Hrw : forall Γ Δ, count_occ φ_eq_dec (Γ ++ Δ) A = count_occ φ_eq_dec Γ A + count_occ φ_eq_dec Δ A).
  clear; intros Γ Δ; induction Γ as [|B Γ].
    reflexivity.
    simpl; destruct φ_eq_dec; rewrite IHΓ; omega.
simpl in H; rewrite Hrw in H.
apply -> (count_occ_In φ_eq_dec) in Hi; omega.
Qed.

Lemma eval_φ_complete : forall A Γ, (eval_φ A) Γ -> derivation (A :: Γ).
Proof.
induction A; intros Γ HΓ;
  unfold eval_φ in *; fold eval_φ in *; simpl; rewrite syntactic_eq_cons_app.
  (* positive variable *)
  apply HΓ; clear Γ HΓ; intros Γ HΓ; simpl; simpl in HΓ.
  now rewrite syntactic_eq_cons_app; apply HΓ; reflexivity.
  (* negative variable *)
  apply HΓ; clear Γ HΓ; intros Γ HΓ; simpl in *.
  replace (φ_neg v :: Γ) with ((φ_neg v :: nil) ++ Γ) by reflexivity.
  now rewrite HΓ; simpl; apply drv_axm.
  (* 1 *)
  now apply HΓ; clear Γ HΓ; intros Γ HΓ; rewrite HΓ; constructor.
  (* ⊥ *)
  now rewrite <- syntactic_eq_cons_app; constructor; rewrite <- app_nil_r; apply HΓ; simpl; reflexivity.
  (* ⊤ *)
  now rewrite <- syntactic_eq_cons_app; constructor.
  (* 0 *)
  now rewrite syntactic_eq_cons_app; apply HΓ; intros Δ HΔ; contradiction.
  (* ⊗ *)
  apply HΓ; clear Γ HΓ; intros Ξ [Γ Δ HΓ HΔ H]; rewrite H; clear Ξ H.
  now simpl; constructor; intuition.
  (* ⅋ *)
  rewrite <- syntactic_eq_cons_app; constructor.
  assert (Hrw : syntactic_eq (A1 :: A2 :: Γ) (Γ ++ A1 :: A2 :: nil)); [|rewrite Hrw; clear Hrw].
    now apply rst_step, synrel_prm, (Permutation.Permutation_app_comm (A1 :: A2 :: nil) Γ).
  apply HΓ; clear Γ HΓ; exists (A1 :: nil) (A2 :: nil); [intros Γ HΓ|intros Γ HΓ|reflexivity].
    now simpl; apply IHA1; assumption.
    now simpl; apply IHA2; assumption.
  (* & *)
  rewrite <- syntactic_eq_cons_app.
  now constructor; rewrite syntactic_eq_cons_app; apply HΓ; [left|right]; assumption.
  (* ⊕ *)
  apply HΓ; clear Γ HΓ.
  intros Γ [HΓ|HΓ]; simpl; [apply drv_pls_1|apply drv_pls_2]; intuition.
  (* ! *)
  apply HΓ; clear Γ HΓ; intros Γ [HΓ HΓ1 HΓd]; simpl.
  apply syntactic_eq_idempotent in HΓd; destruct HΓd as [Γ' Hrw]; rewrite Hrw.
  now constructor; apply IHA; rewrite <- Hrw; assumption.
  (* ? *)
  apply HΓ; clear Γ HΓ; split.
    now intros Γ HΓ; simpl; apply drv_drl; intuition.
    now intros Γ HΓ; simpl; apply drv_wkn; rewrite <- app_nil_r; apply HΓ; simpl; reflexivity.
    now simpl; apply rst_step, synrel_ctr.
Qed.

End Completeness.

End Phase_semantics.
