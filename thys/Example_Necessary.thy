theory Example_Necessary
  imports Computation
begin

(* Example 19 *)

datatype states = Init | Copy bool | Skip bool | Check bool | Accept

instantiation states :: finite
begin

instance
proof (standard)
  have "(UNIV :: states set) \<subseteq> {Init, Copy True, Copy False, Skip True, Skip False,
    Check True, Check False, Accept}"
    using states.exhaust by blast
  then show "finite (UNIV :: states set)"
    using finite_subset by auto
qed

end

type_synonym Sigma = "bool"

inductive delta :: "states \<Rightarrow> Sigma \<Rightarrow> states \<times> Sigma list \<Rightarrow> bool" where
  "delta Init False (Copy False, [False])"
| "delta Init False (Skip True, [])"
| "delta Init True (Skip False, [])"
| "delta Init True (Copy True, [])"
| "delta (Copy False) True (Skip False, [])"
| "delta (Skip True) True (Copy True, [])"
| "delta (Copy b) False (Copy b, [False])"
| "delta (Skip b) False (Skip b, [])"
| "delta (Skip False) True (Check False, [])"
| "delta (Copy True) True (Check True, [])"
| "delta (Check False) False (Accept, [])"
| "delta (Check True) True (Accept, [])"

lemma finite_delta: "finite {x. delta q z x}"
proof -
  have "{x. delta q z x} \<subseteq> UNIV \<times> {xs. length xs \<le> 1}"
    by (auto elim: delta.cases)
  then show ?thesis
    using finite_subset finite_bounded_lists by fastforce
qed

interpretation NFT Init delta "\<lambda>q. q = Accept" UNIV
  using finite_UNIV finite_delta
  by unfold_locales auto

lemma nft_comp_Accept: "computation q (as, bs) q' \<Longrightarrow> q = Accept \<Longrightarrow>
  q' = Accept \<and> as = [] \<and> bs = []"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim: delta.cases)

lemma nft_comp_Check_Accept: "computation q (as, bs) q' \<Longrightarrow> q = Check b \<Longrightarrow>
  q' = Check b \<or> q' = Accept"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim: delta.cases dest: nft_comp_Accept)

lemma nft_comp_Copy_True_Skip: "computation q (as, bs) q' \<Longrightarrow>
  q = Copy True \<Longrightarrow> q' = Skip b \<Longrightarrow> False"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim: delta.cases dest: nft_comp_Check_Accept)

lemma nft_comp_Skip_False_Copy: "computation q (as, bs) q' \<Longrightarrow>
  q = Skip False \<Longrightarrow> q' = Copy b \<Longrightarrow> False"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto elim: delta.cases dest: nft_comp_Check_Accept)

lemma nft_comp_Skip_dest: "computation q (as, bs) q' \<Longrightarrow> q = Skip b \<Longrightarrow> q' = Skip b' \<Longrightarrow>
  as = replicate (length as) False \<and> bs = [] \<and> b = b'"
  by (induction q "(as, bs)" q' arbitrary: as bs b b' rule: computation.induct)
     (auto elim: delta.cases dest: nft_comp_Copy_True_Skip nft_comp_Check_Accept)

lemma nft_comp_Copy_dest: "computation q (as, bs) q' \<Longrightarrow> q = Copy b \<Longrightarrow> q' = Copy b' \<Longrightarrow>
  as = replicate (length as) False \<and> bs = as \<and> b = b'"
  by (induction q "(as, bs)" q' arbitrary: as bs b b' rule: computation.induct)
     (auto elim: delta.cases dest: nft_comp_Skip_False_Copy nft_comp_Check_Accept)

lemma nft_comp_Skip_intro: "computation (Skip b) (replicate n False, []) (Skip b)"
  using computation.step delta.intros(8)
  by (induction n) fastforce+

lemma nft_comp_Copy_intro: "computation (Copy b) (replicate n False, replicate n False) (Copy b)"
  using computation.step delta.intros(7)
  by (induction n) fastforce+

lemma sound_True: "(replicate n False @ [True] @ replicate n' False @ [True] @ [False],
  replicate n False) \<in> \<tau>"
  unfolding \<tau>_def
  using comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(3)] nft_comp_Skip_intro] 
        one_step[OF delta.intros(9)]]
        one_step[OF delta.intros(11)]]
        comp_trans[OF comp_trans[OF comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(1)] nft_comp_Copy_intro]
        one_step[OF delta.intros(5)]] nft_comp_Skip_intro]
        one_step[OF delta.intros(9)]]
        one_step[OF delta.intros(11)]]
  by (cases n) auto

lemma sound_False: "(replicate n False @ [True] @ replicate n' False @ [True] @ [True],
  replicate n' False) \<in> \<tau>"
  unfolding \<tau>_def
  using comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(4)] nft_comp_Copy_intro]
        one_step[OF delta.intros(10)]]
        one_step[OF delta.intros(12)]]
        comp_trans[OF comp_trans[OF comp_trans[OF comp_trans[OF comp_trans[OF
        one_step[OF delta.intros(2)] nft_comp_Skip_intro]
        one_step[OF delta.intros(6)]] nft_comp_Copy_intro]
        one_step[OF delta.intros(10)]]
        one_step[OF delta.intros(12)]]
  by (cases n) auto

lemma snd_part:
  assumes "computation q (as, bs) q'" "q = Skip False \<or> q = Copy True"
    "q' = Skip False \<or> q' = Copy True"
  shows "q = q'" "as = replicate (length as) False \<and> bs = (if q = Copy True then as else [])"
proof -
  show q_q': "q = q'"
    using nft_comp_Copy_True_Skip[OF assms(1)] nft_comp_Skip_False_Copy[OF assms(1)] assms(2,3)
    by auto
  show "as = replicate (length as) False \<and> bs = (if q = Copy True then as else [])"
    using assms(2)
  proof (rule disjE)
    assume q_def: "q = Copy True"
    then show "as = replicate (length as) False \<and> bs = (if q = Copy True then as else [])"
      using nft_comp_Copy_dest[OF assms(1) q_def q_q'[symmetric, unfolded q_def]]
      by auto
  next
    assume q_def: "q = Skip False"
    then show "as = replicate (length as) False \<and> bs = (if q = Copy True then as else [])"
      using nft_comp_Skip_dest[OF assms(1) q_def q_q'[symmetric, unfolded q_def]]
      by auto
  qed
qed

lemma fst_part:
  assumes "computation q (as, bs) q'" "q = Copy False \<or> q = Skip True"
    "q' = Skip False \<or> q' = Copy True"
  shows "\<exists>n n'. as = replicate n False @ [True] @ replicate n' False \<and>
    bs = replicate (if q = Copy False then n else n') False"
  using assms
proof (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  case (step q a q' bs as bs' q'')
  show ?case
  proof (cases a)
    case False
    then show ?thesis
      using step nft_comp_Copy_dest nft_comp_Skip_dest
      apply (auto elim!: delta.cases)
      subgoal for n n'
        apply (rule exI[of _ "Suc n"])
        apply auto
        done
      subgoal for n n'
        apply (rule exI[of _ "Suc n"])
        apply auto
        done
      subgoal for n n'
        apply (rule exI[of _ "Suc n"])
        apply auto
        done
      subgoal for n n'
        apply (rule exI[of _ "Suc n"])
        apply auto
        done
      done
  next
    case True
    show ?thesis
      using step
      using snd_part[OF step(2)]
      apply (auto simp add: True elim!: delta.cases)
      apply (rule exI[of _ "0"])
      apply auto
      done
  qed
qed auto

lemma comp_end_Accept:
  assumes "computation q (as, bs) Accept" "q \<noteq> Accept"
  shows "\<exists>as' \<beta>. computation q (as', bs) (Check \<beta>) \<and> as = as' @ [\<beta>]"
  using assms
  apply (induction q as bs Accept rule: comp_rev_induct)
  using assms
    apply (auto elim: delta.cases)
  done

lemma comp_end_Check:
  assumes "computation q (as, bs) (Check b)" "q \<noteq> Check b"
  shows "\<exists>as'. computation q (as', bs) (if b then Copy True else Skip False) \<and> as = as' @ [True]"
  using assms
  apply (induction q as bs "Check b" rule: comp_rev_induct)
  using assms
    apply (auto elim: delta.cases)
  done

lemma completeness:
  assumes "(as, bs) \<in> \<tau>"
  shows "\<exists>n n' \<beta>. as = replicate n False @ [True] @ replicate n' False @ [True] @ [\<beta>] \<and>
    bs = replicate (if \<beta> then n' else n) False"
  using assms
proof (cases as)
  case (Cons a as')
  have comp: "computation Init (a # as', bs) Accept"
    using assms
    unfolding \<tau>_def Cons
    by auto
  obtain q cs cs' where split: "delta Init a (q, cs)" "computation q (as', cs') Accept"
    "bs = cs @ cs'"
    by (rule computation.cases[OF comp(1)]) auto
  show ?thesis
  proof (cases a)
    case False
    then have q_or: "q = Copy False \<or> q = Skip True"
      using split(1)
      by (auto elim: delta.cases)
    have cs_def: "cs = (if q = Copy False then [False] else [])"
      using split(1)
      by (auto simp add: False elim: delta.cases)
    obtain as'' \<beta> where tail: "as' = as'' @ [True] @ [\<beta>]"
      "computation q (as'', cs') (if \<beta> then Copy True else Skip False)"
      using comp_end_Accept[OF split(2)] comp_end_Check q_or
      by fastforce
    obtain n n' where wit: "as'' = replicate n False @ [True] @ replicate n' False"
      "cs' = replicate (if q = Copy False then n else n') False"
      using fst_part[OF tail(2) q_or]
      by fastforce
    have \<beta>_iff: "\<beta> \<longleftrightarrow> q = Skip True"
      using tail(2) q_or
      by (fastforce split: if_splits dest: nft_comp_Copy_dest nft_comp_Skip_dest)
    show ?thesis
      apply (auto simp add: Cons False tail(1) split(3) cs_def wit \<beta>_iff)
      apply (rule exI[of _ "n + 1"])
         apply (auto)[1]
      apply (rule exI[of _ "n + 1"])
      using q_or
      apply auto
      done
  next
    case True
    then have q_or: "q = Skip False \<or> q = Copy True"
      using split(1)
      by (auto elim: delta.cases)
    have cs_def: "cs = []"
      using split(1)
      by (auto simp add: True elim: delta.cases)
    obtain as'' \<beta> where tail: "as' = as'' @ [True] @ [\<beta>]"
      "computation q (as'', cs') (if \<beta> then Copy True else Skip False)"
      using comp_end_Accept[OF split(2)] comp_end_Check q_or
      by fastforce
    define n where "n = length as''"
    have wit: "as'' = replicate n False"
      "cs' = (if q = Copy True then as'' else [])"
      "q = (if \<beta> then Copy True else Skip False)"
      using snd_part[OF tail(2) q_or]
      by (auto simp add: n_def)
    show ?thesis
      using wit(3)
      by (auto simp add: Cons True tail(1) wit(1,2) split(3) cs_def)
  qed
qed (auto simp add: \<tau>_def dest: no_step)

lemma active_Copy: "active (Copy False) []"
  using comp_trans[OF comp_trans[OF one_step[OF delta.intros(5)] one_step[OF delta.intros(9)]]
        one_step[OF delta.intros(11)]]
  by (auto simp add: active_def)

lemma active_Skip: "active (Skip True) (replicate n False)"
  using comp_trans[OF comp_trans[OF comp_trans[OF one_step[OF delta.intros(6)]
        nft_comp_Copy_intro[of True "n"]]
        one_step[OF delta.intros(10)]] one_step[OF delta.intros(12)]]
  by (auto simp add: active_def) (metis append.right_neutral)

lemma correctness: "\<tau> = {(as, bs). \<exists>n n' \<beta>. as = replicate n False @ [True] @
  replicate n' False @ [True] @ [\<beta>] \<and> bs = replicate (if \<beta> then n' else n) False}"
  using sound_True sound_False completeness
  by fastforce

lemma unbounded: "\<not>bounded K"
  unfolding bounded_def
  using comp_trans[OF one_step[OF delta.intros(1)] nft_comp_Copy_intro[of False "K"]]
        active_Copy
        comp_trans[OF one_step[OF delta.intros(2)] nft_comp_Skip_intro[of True "K"]]
        active_Skip[of "K + 1"]
  using impossible_Cons
  by auto fastforce

end
