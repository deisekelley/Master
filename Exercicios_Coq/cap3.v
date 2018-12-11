Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.


Definition mylist := cons 1 (cons 2 (cons 3 nil)).


Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

  Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.


Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.


(*************Exercise: 1 star (snd_fst_is_swap)************)

Inductive natprod : Type := | pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(*************Exercise: 1 star, optional (fst_swap_is_snd)************)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.

(*************Exercise: 2 stars, recommended (list_funs)************)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
 | nil => nil
 | 0::t => nonzeros t 
 | h::t => h :: (nonzeros t)   
 end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
         Proof. reflexivity. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end. 

Definition oddb (n:nat) : bool := negb (evenb n).

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match (oddb h) with 
              | true => h :: oddmembers t
              | false => oddmembers t
              end
  end.    

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.


Fixpoint countoddmembers (l:natlist) : nat :=
  match l with
    | nil => O
    | h::t => match (oddb h) with
                | true =>  S (countoddmembers t)
                | false => countoddmembers t
              end
  end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
    Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
    Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
    Proof. reflexivity. Qed.

(*************Exercise: 3 stars, advanced (alternate)************)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l2 with
    | [] => l1
    | h2::t2 => match l1 with
                  | [] => l2
                  | h1 :: t1 => h1 :: h2 :: (alternate t1 t2)
                end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint count (v:nat) (s:bag) : nat := (*Quantas vezes o numero aparece*)
    match s with    
    | [] => O
    | h::t => if beq_nat v h then S (count v t) else count v t
    end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
 Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.

(**************************** BAGS ***************************************)
Definition sum : bag -> bag -> bag := app.
 
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
 Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=  cons v s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=  negb (beq_nat (count v s) O).

Example test_member1: member 1 [1;4;1] = true.
 Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
 Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
      match s with
      | [] => []
      | h::t => if (beq_nat h v) then t else h ::(remove_one v t)
      end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
   Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
   Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
   Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
   Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (beq_nat h v) then (remove_all v t) else h::(remove_all v t)
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | [] => true
    | h::t => if (member h s2) then (subset t (remove_one h s2)) else false
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
 Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
 Proof. reflexivity. Qed.

(*************Exercise: 3 stars (list_exercises)************)

Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros m n.  induction n as [| n' IHn'].
  + simpl. rewrite plus_n_O. reflexivity.
  + simpl. rewrite <- IHn'. rewrite plus_n_Sm. reflexivity. Qed.


Theorem app_nil_r : forall l : natlist, l ++ [] = l.
Proof.
   intros l. induction l as [| n l' IHl'].
   - reflexivity.
   - simpl. rewrite -> IHl'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.


Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.
  
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite <- app_assoc. rewrite -> IHl1'. reflexivity. Qed.

Theorem rev_involutive : forall l : natlist, rev (rev l) = l.
Proof.
  intros l. induction l as [| n l IHl].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl. reflexivity. Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. rewrite <- app_assoc. rewrite <- app_assoc. reflexivity. Qed.

Lemma nonzeros_app : forall l1 l2 : natlist, 
nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros l1. induction l1 as [| n l1' IHl1'].
  - intros l2. reflexivity.
  - intros l2. simpl. destruct n. apply IHl1'. simpl. rewrite <- (IHl1' l2). reflexivity. Qed.
 

(*************Exercise: 2 stars (beq_natlist)************)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1,l2 with
  | nil,nil => true
  | h1 :: t1, h2 :: t2 => if beq_nat h1 h2 then beq_natlist t1 t2 else false
  | _,_ => false
  end.


Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* FILL IN HERE *) Admitted.
Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Definition hd_error (l : natlist) : natoption  :=
  match l with
  | nil => None
  | h :: t => Some h
  end.
 
Example test_hd_error1 : hd_error [] = None.
 Proof. simpl. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
 Proof. simpl. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
 Proof. simpl. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l default. induction l as [| n l IHl].
  - reflexivity.
  - reflexivity.
Qed. 

Inductive id : Type :=
  | Id : nat -> id.

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.



