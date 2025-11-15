From stdpp Require Import coPset.
From iris.bi.lib Require Export atomic.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.base_logic Require Import invariants.


Section invariants.
  Context {PROP : bi} `{!BiFUpd PROP} {TA TB : tele}.
  Implicit Types
    (E : coPset) (* outer/inner masks *)
    (α : TA → PROP) (* atomic pre-condition *)
    (β : TA → TB → PROP) (* atomic post-condition *)
    (Φ : TA → TB → PROP) (* post-condition *)
  .

  Definition is_invariant α := (∃.. x, α x)%I.
  Definition from_effect β Ψ := λ x y, (β x y ∗ (β x y -∗ Ψ))%I.
  
  Definition atomic_resource Eo Ei α Ψ :=
    atomic_update Eo Ei α
      (λ x _, α x)
      (λ (_ : TA) (_ : TB), Ψ).
  Definition atomic_effect E Ψ α :=
    (Ψ ∗ (Ψ ={E}=∗ is_invariant α))%I.
  Definition atomic_invariant Eo Ei α β Φ :=
    atomic_update Eo Ei α
      (λ x y, atomic_effect (⊤ ∖ Eo) (β x y) α)
      (λ x y, atomic_resource Eo Ei α (Φ x y)).

  Lemma aupd_intro Eo Ei α β Φ :
    Ei ⊆ Eo →
    (∃.. x, α x ∗ (∀.. y, β x y -∗ Φ x y)) -∗
    atomic_update Eo Ei α β Φ.
  Proof.
    iIntros (HE) "(%x & Hα & HΦ)".
    iAuIntro. iAaccIntro with "Hα".
    + iIntros "Hα". iModIntro. iFrame.
    + iIntros (y) "Hβ". iModIntro. by iApply "HΦ".
  Qed.

  Lemma ares_intro Eo Ei α Ψ :
    Ei ⊆ Eo →
    (is_invariant α ∗ (is_invariant α -∗ Ψ)) -∗
    atomic_resource Eo Ei α Ψ.
  Proof.
    iIntros (HE) "([%x Hα] & HΨ)".
    iApply aupd_intro; first done.
    iExists x. iFrame. iIntros "% Hα".
    iApply "HΨ". by iExists x.
  Qed.

  Lemma aeff_intro E Ψ α :
    (Ψ ∗ (Ψ -∗ is_invariant α)) -∗
    atomic_effect E Ψ α.
  Proof.
    iIntros "[HΨ Hα]". iFrame.
    iIntros "HΨ". iApply "Hα". by iFrame.
  Qed.

  Lemma ainv_intro Eo Ei α β Φ :
    Ei ⊆ Eo →
    (∃.. x, α x ∗ (∀.. y, β x y -∗ β x y ∗ (is_invariant α -∗ Φ x y))) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof.
    iIntros (HE) "(%x & Hα & HΦ)".
    iApply aupd_intro; first done.
    iExists x. iFrame. iIntros (y) "[Hβ Hα]".
    iDestruct ("HΦ" with "Hβ") as "[Hβ HΦ]".
    iApply ares_intro; first done.
    iDestruct ("Hα" with "Hβ") as "Hα".
    iFrame.
  Admitted.

  Lemma ainv_intro_alt Eo Ei α β Φ :
    Ei ⊆ Eo →
    (∃.. x, α x ∗ (∀.. y, is_invariant α -∗ Φ x y)) -∗
    atomic_invariant Eo Ei α β Φ.
  Proof.
    iIntros (HE) "(%x & Hα & HΦ)".
    iApply ainv_intro; first done.
    iExists x. iFrame. iIntros "% Hβ".
    iFrame. iApply "HΦ".
  Qed.
End invariants.

Definition atomic_wp `{!irisGS_gen hlc Λ Σ} {TA TB TP : tele}
  (e: expr Λ) (* expression *)
  (E : coPset) (* *implementation* mask *)
  (α: TA → iProp Σ) (* atomic pre-condition *)
  (β: TA → TB → iProp Σ) (* atomic post-condition *)
  (POST: TA → TB → TP → option (iProp Σ)) (* non-atomic post-condition *)
  (f: TA → TB → TP → val Λ) (* Turn the return data into the return value *)
  : iProp Σ :=
    ∀ (Φ : val Λ → iProp Σ),
            (* The (outer) user mask is what is left after the implementation
            opened its things. *)
            atomic_invariant (⊤∖E) ∅ α β (λ.. x y, ∀.. z, POST x y z -∗? Φ (f x y z)) -∗
            WP e {{ Φ }}.

(** Notation: Atomic invariants *)
Notation "'AI' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app $ λ x1, .. (λ xn,
                        tele_app (λ y1, .. (λ yn, β%I) .. )
                        ) .. )
                (tele_app $ λ x1, .. (λ xn,
                        tele_app (λ y1, .. (λ yn, Φ%I) .. )
                        ) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder, y1 binder, yn binder,
  format "'[hv   ' 'AI'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                (TB:=TeleO)
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
                (tele_app $ λ x1, .. (λ xn, tele_app Φ%I) .. )
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, x1 binder, xn binder,
  format "'[hv   ' 'AI'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' α '}>' @ Eo , Ei '<{' ∀∀ y1 .. yn , β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleO)
                (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
                Eo Ei
                (tele_app α%I)
                (tele_app $ tele_app (λ y1, .. (λ yn, β%I) ..))
                (tele_app $ tele_app (λ y1, .. (λ yn, Φ%I) ..))
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200, y1 binder, yn binder,
  format "'[hv   ' 'AI'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' ∀∀  y1  ..  yn ,  '/' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

Notation "'AI' '<{' α '}>' @ Eo , Ei '<{' β , 'COMM' Φ '}>'" :=
  (atomic_invariant (TA:=TeleO) (TB:=TeleO)
                Eo Ei
                (tele_app α%I)
                (tele_app $ tele_app β%I)
                (tele_app $ tele_app Φ%I)
  )
  (at level 20, Eo, Ei, α, β, Φ at level 200,
  format "'[hv   ' 'AI'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '[' β ,  '/' COMM  Φ  ']' '}>' ']'") : bi_scope.

(** Notation: Atomic resources *)
Notation "'AR' '<{' ∃∃ x1 .. xn , α '}>' @ Eo , Ei '<{' Ψ '}>'" :=
  (atomic_resource (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
                Eo Ei
                (tele_app $ λ x1, .. (λ xn, α%I) ..)
                (tele_app Ψ%I)
  )
  (at level 20, Eo, Ei, α, Ψ at level 200, x1 binder, xn binder,
  format "'[hv   ' 'AR'  '<{'  '[' ∃∃  x1  ..  xn ,  '/' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '['  Ψ  ']' '}>' ']'") : bi_scope.

Notation "'AR' '<{' α '}>' @ Eo , Ei '<{' Ψ '}>'" :=
  (atomic_resource (TA:=TeleO)
                Eo Ei
                (tele_app α%I)
                (tele_app Ψ%I)
  )
  (at level 20, Eo, Ei, α, Ψ at level 200,
  format "'[hv   ' 'AR'  '<{'  '[' α  ']' '}>'  '/' @  '[' Eo ,  '/' Ei ']'  '/' '<{'  '['  Ψ  ']' '}>' ']'") : bi_scope.

(** Notation: Atomic triples *)
(** We avoid '<<{'/'}>>' since those can also reasonably be infix operators
(and in fact Autosubst uses the latter). *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' z1 .. zn , 'RET' v ; POST '}>>'" :=
(* The way to read the [tele_app foo] here is that they convert the n-ary
function [foo] into a unary function taking a telescope as the argument. *)
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleS (λ z1, .. (TeleS (λ zn, TeleO)) .. ))
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, Some POST%I) ..
                                  ) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn,
                                   tele_app $ λ z1, .. (λ zn, v%V) ..
                                  ) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder, z1 binder, zn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' z1  ..  zn ,  RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* There are overall 16 of possible variants of this notation:
- with and without ∀∀ binders
- with and without ∃∃ binders
- with and without RET binders
- with and without POST

However we don't support the case where RET binders are present but anything
else is missing. Below we declare the 8 notations that involve no RET binders.
*)

(* No RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app $ v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ Some POST%I
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ tele_app $ v%V
                        ) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ Some POST%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app $ v%V) .. )
  )
  (at level 20, E, β, α, v, POST at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v ; POST '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app $ Some POST%I)
             (tele_app $ tele_app $ tele_app $ v%V)
  )
  (at level 20, E, β, α, v, POST at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v ;  '/' POST  ']' '}>>' ']'")
  : bi_scope.

(* No RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, β%I) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app None) ..
                        ) .. )
             (tele_app $ λ x1, .. (λ xn,
                         tele_app $ λ y1, .. (λ yn, tele_app v%V) ..
                        ) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' ∀∀ x1 .. xn , α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleS (λ x1, .. (TeleS (λ xn, TeleO)) .. ))
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app $ λ x1, .. (λ xn, α%I) ..)
             (tele_app $ λ x1, .. (λ xn, tele_app β%I) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app None) .. )
             (tele_app $ λ x1, .. (λ xn, tele_app $ tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, x1 binder, xn binder,
   format "'[hv' '<<{'  '[' ∀∀  x1  ..  xn ,  '/' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' ∃∃ y1 .. yn , β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleS (λ y1, .. (TeleS (λ yn, TeleO)) .. ))
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app $ λ y1, .. (λ yn, β%I) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app None) .. )
             (tele_app $ tele_app $ λ y1, .. (λ yn, tele_app v%V) .. )
  )
  (at level 20, E, β, α, v at level 200, y1 binder, yn binder,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' ∃∃  y1  ..  yn ,  '/' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.

(* No ∀∀ binders, no ∃∃ binders, no RET binders, no POST *)
Notation "'<<{' α '}>>' e @ E '<<{' β '|' 'RET' v '}>>'" :=
  (atomic_wp (TA:=TeleO)
             (TB:=TeleO)
             (TP:=TeleO)
             e%E
             E
             (tele_app α%I)
             (tele_app $ tele_app β%I)
             (tele_app $ tele_app $ tele_app None)
             (tele_app $ tele_app $ tele_app v%V)
  )
  (at level 20, E, β, α, v at level 200,
   format "'[hv' '<<{'  '[' α  ']' '}>>'  '/  ' e  @  E  '/' '<<{'  '[' β  '|'  '/' RET  v  ']' '}>>' ']'")
  : bi_scope.



(** Theory *)
Section lemmas.
  Context `{!irisGS_gen hlc Λ Σ} {TA TB TP : tele}.
  Notation iProp := (iProp Σ).
  Implicit Types (α : TA → iProp) (β : TA → TB → iProp) (POST : TA → TB → TP → option iProp) (f : TA → TB → TP → val Λ).

  (* Atomic triples imply sequential triples. *)
  Lemma atomic_wp_seq e E α β POST f :
    atomic_wp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗
    (∀.. y, from_effect β (is_invariant α -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) x y) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros "Hwp" (Φ x) "Hα HΦ".
    iApply (wp_frame_wand with "HΦ"). iApply "Hwp".
    iApply ainv_intro; first by set_solver.
    iExists x. iFrame. iIntros (y) "Hβ".
    iFrame. iIntros "Hα".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite -> !tele_app_bind. iIntros (z) "Hpost HΦ".
    iDestruct ("HΦ" $! y) as "[Hβ HΦ]".
    iApply ("HΦ" with "Hβ Hα Hpost").
  Qed.

  (** This version matches the Texan triple, i.e., with a later in front of the
  [(∀.. y, β x y -∗ Φ (f x y))]. *)
  Lemma atomic_wp_seq_step e E α β POST f :
    TCEq (to_val e) None →
    atomic_wp e E α β POST f -∗
    ∀ Φ, ∀.. x, α x -∗
    ▷ (∀.. y, from_effect β (is_invariant α -∗ ∀.. z, POST x y z -∗? Φ (f x y z)) x y) -∗
    WP e {{ Φ }}.
  Proof.
    iIntros (?) "Hwp"; iIntros (Φ x) "Hα HΦ".
    iApply (wp_step_fupd _ _ ⊤ _ (∀.. y : TB, _)
      with "[$HΦ //]"); first done. iApply "Hwp".
    iApply ainv_intro; first by set_solver.
    iExists x. iFrame. iIntros (y) "Hβ".
    iFrame. iIntros "Hα".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite -> !tele_app_bind. iIntros (z) "Hpost HΦ".
    iDestruct ("HΦ" $! y) as "[Hβ HΦ]".
    iApply ("HΦ" with "Hβ Hα Hpost").
  Qed.

  (* Sequential triples with the empty mask for a physically atomic [e] are atomic. *)
  (* Lemma atomic_seq_wp_atomic e E α β POST f `{!Atomic WeaklyAtomic e} :
    (∀ Φ, ∀.. x, α x -∗ (∀.. x', α x' -∗ ∀.. y z, POST x y z -∗? Φ (f x y z)) -∗ WP e @ ∅ {{ Φ }}) -∗
    atomic_wp e E α β POST f.
  Proof.
    iIntros "Hwp" (Φ) "AI". iMod "AI" as (x) "[Hα [_ Hclose]]".
    iApply ("Hwp" with "Hα"). iIntros "%x' Hα %y %z Hpost".
    iMod ("Hclose" with "Hα") as "HΦ".
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed. *)

  (** Sequential triples with a persistent precondition and no initial quantifier
  are atomic. *)
  (* Lemma persistent_seq_wp_atomic e E (α : [tele] → iProp) (β : [tele] → TB → iProp)
      (POST : [tele] → TB → TP → option iProp) (f : [tele] → TB → TP → val Λ)
      {HP : Persistent (α [tele_arg])} :
    (∀ Φ, α [tele_arg] -∗ (∀.. y, β [tele_arg] y -∗ ∀.. z, POST [tele_arg] y z -∗? Φ (f [tele_arg] y z)) -∗ WP e {{ Φ }}) -∗
    atomic_wp e E α β POST f.
  Proof.
    simpl in HP. iIntros "Hwp" (Φ) "HΦ". iApply fupd_wp.
    iMod ("HΦ") as "[#Hα [Hclose _]]". iMod ("Hclose" with "Hα") as "HΦ".
    iApply wp_fupd. iApply ("Hwp" with "Hα"). iIntros "!> %y Hβ %z Hpost".
    iMod ("HΦ") as "[_ [_ Hclose]]". iMod ("Hclose" with "Hβ") as "HΦ".
    (* FIXME: Using ssreflect rewrite does not work, see Coq bug #7773. *)
    rewrite ->!tele_app_bind. iApply "HΦ". done.
  Qed. *)

  (* Lemma atomic_wp_mask_weaken e E1 E2 α β POST f :
    E1 ⊆ E2 → atomic_wp e E1 α β POST f -∗ atomic_wp e E2 α β POST f.
  Proof.
    iIntros (HE) "Hwp". iIntros (Φ) "AU". iApply "Hwp".
    iApply atomic_update_mask_weaken; last done. set_solver.
  Qed. *)

  (** We can open invariants around atomic triples.
      (Just for demonstration purposes; we always use [iInv] in proofs.) *)
  Lemma atomic_wp_inv e E α β POST f N I :
    ↑N ⊆ E →
    atomic_wp e (E ∖ ↑N) (λ.. x, ▷ I ∗ α x) (λ.. x y, ▷ I ∗ β x y) POST f -∗
    inv N I -∗ atomic_wp e E α β POST f.
  Proof.
    intros ?. iIntros "Hwp #Hinv" (Φ) "AU". iApply "Hwp".
    unfold atomic_invariant; iAuIntro.
    iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
    iIntros (x) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
    - (* abort *)
      iIntros "[HI $]". by eauto with iFrame.
    - (* commit *)
      iIntros (y) "Heff"; rewrite ->!tele_app_bind.
      iModIntro. iRight. iExists y; rewrite ->!tele_app_bind.
      assert (∀ Y : coPset, (⊤ ∖ (⊤ ∖ Y)) = Y) as Hdiff.
      {
        intros Y. by rewrite difference_difference_r_L
          difference_diag_L union_empty_l_L
          comm_L -subseteq_intersection_L.
      }
      rewrite ?Hdiff.
      iAssert (atomic_effect E (β x y) α ∗ ▷ I)%I with "[-]" as "[Heff HI]".
      {
        iDestruct "Heff" as "[[? ?] Heff]"; iFrame.
        iIntros "Hβ". iInv N as "HI".
        iMod ("Heff" with "[$]") as (z) "Hα".
        rewrite ->!tele_app_bind; iDestruct "Hα" as "[HI Hα]".
        iModIntro. iFrame. iModIntro. by iExists z.
      }

      iFrame. iIntros "AU". iModIntro.
      unfold atomic_resource; iAuIntro.
      iInv N as "HI". iApply (aacc_aupd with "AU"); first solve_ndisj.
      iIntros (z) "Hα". iAaccIntro with "[HI Hα]"; rewrite ->!tele_app_bind; first by iFrame.
      * iIntros "[HI $]". by eauto with iFrame.
      * iIntros (w) "[HI Hα]". iModIntro.
        rewrite ->!tele_app_bind. iRight. iExists w. iFrame. iIntros.
        iModIntro. done.
  Qed.

End lemmas.
