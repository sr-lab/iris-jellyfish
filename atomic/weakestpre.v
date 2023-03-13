From stdpp Require Import namespaces.
From iris.bi Require Import telescopes.
From iris.proofmode Require Import proofmode classes.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants.
From iris.prelude Require Import options.

From SkipList.atomic Require Export update.

(* This hard-codes the inner mask to be empty, because we have yet to find an
example where we want it to be anything else. *)
Definition atomic_wp `{!irisGS_gen hlc Λ Σ} {TA TB TC : tele}
  (e: expr Λ) (* expression *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (Q: TB → iProp Σ) (* private post-condition *)
  (Ψ: TC → iProp Σ)
  (f: TA → TB → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val Λ → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_update (⊤∖E) ∅ α Ψ β (λ.. x y, Q y ={⊤∖E}=∗ Φ (f x y)) -∗
            WP e {{ Φ }}.
(* Note: To add a private postcondition, use
   atomic_update α β Eo Ei (λ x y, POST x y -∗ Φ (f x y)) *)

(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β , 'RET' v '>>>' {{{ Q } } }" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TC:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
             (tele_app $ λ y1, .. (λ yn, Q%I) ..)
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app (λ y1, .. (λ yn, v%V) .. )
                        ) .. )
  )
  (at level 20, E, α, β, Q, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  @  E  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β ,  '/' 'RET'  v  ']' '>>>' {{{ '[' Q ']' } } } ']'")
  : bi_scope.

Notation "'<<<' ∀∀ x1 .. xn , α '>>>' e @ E '<<<' β , 'RET' v '>>>' {{{ Q } } }" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TC:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app Q%I)
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app v%V) .. )
  )
  (at level 20, E, α, β, Q, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<<'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '>>>'  '/  ' e  @  E  '/' '<<<'  '[' β ,  '/' 'RET'  v  ']' '>>>' {{{ '[' Q ']' } } } ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ E '<<<' ∃∃ y1 .. yn , β , 'RET' v '>>>' {{{ Q } } }" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TC:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app (λ y1, .. (λ yn, β%I) .. ))
             (tele_app $ λ y1, .. (λ yn, Q%I) ..)
             (tele_app α%I)
             (tele_app $ tele_app (λ y1, .. (λ yn, v%V) .. ))
  )
  (at level 20, E, α, β, Q, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<<'  '[' α  ']' '>>>'  '/  ' e  @  E  '/' '<<<'  '[' ∃∃  y1  ..  yn ,  '/' β ,  '/' 'RET'  v  ']' '>>>' {{{ '[' Q ']' } } } ']'")
  : bi_scope.

Notation "'<<<' α '>>>' e @ E '<<<' β , 'RET' v '>>>' {{{ Q } } }" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TC:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app Q%I)
             (tele_app α%I)
             (tele_app $ tele_app v%V)
  )
  (at level 20, E, α, β, Q, v at level 200,
   format "'[hv' '<<<'  '[' α  ']' '>>>'  '/  ' e  @  E  '/' '<<<'  '[' β ,  '/' 'RET'  v  ']' '>>>' {{{ '[' Q ']' } } } ']'")
  : bi_scope.

(** Theory *)
Section lemmas.
  Context `{!irisGS_gen hlc Λ Σ} {TA TB TC : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (Q : TB → iProp) (Ψ : TC → iProp) (f : TA → TB → val Λ).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_wp_seq e E α β Q Ψ f :
    atomic_wp e E α β Q Ψ f -∗
    ∀ Φ, ∀.. x, α x -∗
    (∀.. y, β x y -∗ (Q y -∗ Φ (f x y))) -∗
    (∀.. y, β x y -∗ ∃.. z, Ψ z ∗ (Ψ z -∗ β x y)) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ HΨ".
    iApply (wp_frame_wand with "HΦ"). iApply "Hwp".
    iAuIntro. iAaccIntro with "Hα". 
    { iIntros; iModIntro; iFrame. }
    iIntros (y) "Hβ !>".
    iDestruct ("HΨ" with "Hβ") as (z) "[HΨ Hβ]".
    iExists z. iFrame "HΨ". iIntros "HΨ".
    rewrite ->!tele_app_bind. iIntros "HQ !> HΦ".
    iDestruct ("Hβ" with "HΨ") as "Hβ".
    iApply ("HΦ" with "Hβ HQ").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e E α β Q Ψ f :
    TCEq (to_val e) None →
    atomic_wp e E α β Q Ψ f -∗
    ∀ Φ, ∀.. x, α x -∗
    ▷ (∀.. y, β x y -∗ (Q y -∗ Φ (f x y))) -∗
    (∀.. y, β x y -∗ ∃.. z, Ψ z ∗ (Ψ z -∗ β x y)) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros (?) "H"; iIntros (Φ x) "Hα HΦ HΨ".
    iApply (wp_step_fupd _ _ ⊤ _ (∀.. y, β x y -∗ (Q y -∗ Φ (f x y)))
      with "[$HΦ //]"); first done.
    iApply (atomic_wp_seq with "H Hα [] HΨ").
    iIntros (y) "Hβ HQ HΦ". iModIntro.
    iApply ("HΦ" with "Hβ HQ").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  Lemma atomic_seq_wp_atomic e E α β Q Ψ f `{!Atomic WeaklyAtomic e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. y, β x y -∗ (Q y -∗ Φ (f x y))) -∗ WP e @ ∅ {{ Φ }}) -∗
    atomic_wp e E α β Q Ψ f.
  Proof.
    iIntros "Hwp" (Φ) "AU". iMod "AU" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros (y) "Hβ HQ".
    iMod ("Hclose" with "Hβ") as "AP". rewrite ->!tele_app_bind. 
    iMod "AP" as (z) "[HΨ [_ HΦ]]". iMod ("HΦ" with "HΨ") as "HΦ".
    iDestruct ("HΦ" with "HQ") as "HΦ".
    iApply fupd_mask_mono; last by iFrame.
    solve_ndisj.
  Qed.

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  Lemma persistent_seq_wp_atomic e E (α : [tele] → iProp) 
        (β : [tele] → TB → iProp) (Q : TB → iProp) Ψ
        (f : [tele] → TB → val Λ) {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ 
      (∀.. y, β [tele_arg] y -∗ (Q y -∗ Φ (f [tele_arg] y))) -∗ WP e {{ Φ }}
    ) -∗
    atomic_wp e E α β Q Ψ f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!>" (y) "Hβ HQ".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    rewrite ->!tele_app_bind. iMod "HΦ" as (z) "[HΨ [_ HΦ]]".
    iMod ("HΦ" with "HΨ") as "HΦ". iDestruct ("HΦ" with "HQ") as "HΦ".
    iApply fupd_mask_mono; last by iFrame.
    solve_ndisj.
  Qed.

  Lemma atomic_wp_mask_weaken e E1 E2 α β Q Ψ f :
    E1 ⊆ E2 → atomic_wp e E1 α β Q Ψ f -∗ atomic_wp e E2 α β Q Ψ f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply (atomic_update_mask_weaken (⊤ ∖ E2)); first solve_ndisj.
    iApply (atomic_update_wand with "[] AU").
    iIntros (x y) "HΦ". rewrite ->!tele_app_bind.
    iIntros "HQ". iDestruct ("HΦ" with "HQ") as "HΦ".
    iApply fupd_mask_mono; last by iFrame.
    solve_ndisj.
  Qed.

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_wp_inv e E α β Q f N I :
    ↑N ⊆ E →
    atomic_wp e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) Q (λ.. x, ▷ I ∗ α x) f -∗
    inv N I -∗ atomic_wp e E α β Q α f.
  Proof.
    iIntros "%HE Hwp #Hinv" (Φ) "AU". iApply "Hwp".
    replace (⊤ ∖ E) with (⊤ ∖ (E ∖ ↑N) ∖ ↑N) by set_solver.
    iApply (aupd_inv with "Hinv AU"); solve_ndisj.
  Qed.

  Lemma atomic_wp_inv_timeless e E α β Q f N I `{!Timeless I} :
    ↑N ⊆ E →
    atomic_wp e (E ∖ ↑N) (λ.. x, I ∗ α x) (λ.. x y, I ∗ β x y) Q (λ.. x, I ∗ α x) f -∗
    inv N I -∗ atomic_wp e E α β Q α f.
  Proof.
    iIntros "%HE Hwp #Hinv" (Φ) "AU". iApply "Hwp".
    replace (⊤ ∖ E) with (⊤ ∖ (E ∖ ↑N) ∖ ↑N) by set_solver.
    iApply (aupd_inv_timeless with "Hinv AU"); solve_ndisj.
  Qed.

End lemmas.