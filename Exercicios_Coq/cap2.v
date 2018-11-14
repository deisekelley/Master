(*************Exercise: 2 stars, recommended (basic_induction)************)
Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn']. (*O que virou oque?
                                         Ele sabe que o numero vai ser quebrado
                                         pra 0 ou Sn'?*)
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat, n * 0 = 0.
Proof.
   intros n. induction n as [ | n' IHn'].
   - reflexivity.
   - simpl. assumption. Qed.


Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
   intros n m. induction n as [| n' IHn'].
    - simpl. reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
Qed.


Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros m n.  induction n as [| n' IHn'].
  + simpl. rewrite plus_n_O. reflexivity.
  + simpl. rewrite <- IHn'. rewrite plus_n_Sm. reflexivity. Qed.


Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn']. 
   + reflexivity.
   + simpl. rewrite -> IHn'. reflexivity. Qed.

(*************Exercise: 2 stars, recommended (double_plus)************)
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity. Qed.

(*************Exercise: 2 stars, optional (evenb_S)************)

Fixpoint evenb (n:nat) : bool := (*Verifica se é par*)
  match n with 
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Theorem negb_involutive : forall b : bool, negb (negb b) = b.
Proof.
  intros b. destruct b.
  - reflexivity.
  - reflexivity. Qed.



Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl. rewrite negb_involutive. reflexivity. Qed.

(*************Exercise: 1 star (destruct_induction)************)

(*A diferença é que no induct sempre tem uma hipótese, a hipótese de indução, e 
dois casos únicos, o caso do elemento mais simples(caso base) e o caso que a 
a partir de n voce pode provar n + 1. Já o destruct pode ter um número maior 
de casos e ele não supõe uma hipótese.*)



