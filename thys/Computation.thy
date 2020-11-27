theory Computation
  imports Main
begin

lemma split_app: "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>ds. xs' = xs @ ds"
  by (metis (full_types) append_eq_append_conv_if append_eq_conv_conj)

lemma split_app': "\<And>xs ys xs' ys'. xs @ ys = xs' @ ys' \<Longrightarrow> length xs \<le> length xs' \<Longrightarrow>
  \<exists>es. ys = es @ ys'"
  by (simp add: append_eq_append_conv_if)

lemma app_decomp: "length xs = length (ys @ ys') \<Longrightarrow>
  \<exists>zs zs'. xs = zs @ zs' \<and> length zs = length ys \<and> length zs' = length ys'"
  by (metis append_eq_conv_conj length_drop length_rev rev_take)

lemma singleton_dest: "length xs = Suc 0 \<Longrightarrow> \<exists>x. xs = [x]"
  by (cases xs) auto

lemma set_zip: "set (zip xs ys) \<subseteq> set xs \<times> set ys"
  by (induction xs arbitrary: ys) (auto dest: set_zip_leftD set_zip_rightD)

lemma map_ext:
  assumes "map f xs = ys @ ys'"
  shows "\<exists>zs zs'. xs = zs @ zs' \<and> map f zs = ys \<and> map f zs' = ys'"
proof -
  define zs where "zs = take (length ys) xs"
  define zs' where "zs' = drop (length ys) xs"
  have "xs = zs @ zs'" "map f zs = ys" "map f zs' = ys'"
    using iffD1[OF append_eq_conv_conj, OF assms[symmetric]]
    by (auto simp add: zs_def zs'_def take_map drop_map)
  then show ?thesis
    by auto
qed

fun iter_concat :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "iter_concat 0 xs = []"
| "iter_concat (Suc n) xs = xs @ iter_concat n xs"

lemma iter_concat_length: "length (iter_concat n xs) = n * length xs"
  by (induction n xs rule: iter_concat.induct) auto

lemma card_finite_product_subset:
  "finite Q \<Longrightarrow> QS' \<subseteq> Q \<times> Q \<Longrightarrow> card QS' \<le> card Q * card Q"
  by (metis card_cartesian_product card_mono finite_cartesian_product)

lemma finite_bounded_lists: "finite {bs :: ('b :: finite) list. length bs \<le> n}"
proof (induction n)
  case (Suc n)
  have split: "{bs :: 'b list. length bs \<le> Suc n} = {bs. length bs \<le> n} \<union> {bs. length bs = Suc n}"
    by auto
  have "{bs :: 'b list. length bs = Suc n} \<subseteq> (\<Union>(b, bs) \<in> UNIV \<times> {bs. length bs \<le> n}. {b # bs})"
  proof (rule subsetI)
    fix x
    assume "x \<in> {bs :: 'b list. length bs = Suc n}"
    then show "x \<in> (\<Union>(b, bs)\<in>UNIV \<times> {bs. length bs \<le> n}. {b # bs})"
      by (cases x) auto
  qed
  moreover have "finite (\<Union>(b, bs) \<in> UNIV \<times> {bs :: 'b list. length bs \<le> n}. {b # bs})"
    using Suc by auto
  ultimately have "finite {bs :: 'b list. length bs = Suc n}"
    using infinite_super by blast
  with Suc split show ?case
    by auto
qed auto

datatype 'a Al = Symb 'a | Blank

definition "safe_hd bs' = (case bs' of [] \<Rightarrow> Blank | b # bs \<Rightarrow> Symb b)"

lemma safe_hd_Nil: "safe_hd [] = Blank"
  by (auto simp add: safe_hd_def)

lemma safe_hd_Cons: "safe_hd (x # xs) = Symb x"
  by (auto simp: safe_hd_def)

lemma safe_hd_eq: "xs = xs' @ (q, b) # xs'' \<Longrightarrow>
  safe_hd (map snd xs) = safe_hd (map snd (xs' @ (q, b) # xs'''))"
  by (auto simp add: safe_hd_def split: list.splits) (metis Cons_eq_append_conv nth_Cons_0)

lemma safe_hd_app: "safe_hd xs = safe_hd xs' \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs' @ ys)"
  by (auto simp add: safe_hd_def split: list.splits)

lemma safe_hd_app': "safe_hd ys = safe_hd ys' \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs @ ys')"
  by (auto simp add: safe_hd_def split: list.splits) (metis append_Nil hd_append2 list.sel(1))

lemma safe_hd_app'': "xs \<noteq> [] \<Longrightarrow> safe_hd (xs @ ys) = safe_hd (xs @ ys')"
  by (cases xs) (auto simp add: safe_hd_def split: list.splits)

lemma safe_hd_app_Cons: "safe_hd (xs @ x # ys) = safe_hd (xs @ x # ys')"
  by (cases xs) (auto simp add: safe_hd_def split: list.splits)

lemma safe_hd_Nil_dest: "safe_hd [] = safe_hd xs \<Longrightarrow> xs = []"
  by (auto simp: safe_hd_def split: list.splits)

lemma safe_hd_Cons_app: "xs = x # xs' \<Longrightarrow> safe_hd (xs @ ys) = Symb x"
  by (auto simp: safe_hd_def)

(* Definition 1 *)

locale TDFA =
  fixes init :: "'s"
    and \<delta> :: "'s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('s \<times> bool \<times> bool) option"
    and accept :: "'s \<Rightarrow> bool"
    and Q :: "'s set"
  assumes finite_Q: "finite Q" and
    init_in_Q: "init \<in> Q" and
    closed: "q \<in> Q \<Longrightarrow> \<delta> q z = Some (q', b1, b2) \<Longrightarrow> q' \<in> Q" and
    move_left: "\<delta> q (a, b) = Some (q', True, b2) \<Longrightarrow> a \<noteq> Blank" and
    move_right: "\<delta> q (a, b) = Some (q', b1, True) \<Longrightarrow> b \<noteq> Blank" and
    no_step: "\<delta> q (a, b) = Some (q', False, False) \<Longrightarrow> False"
begin

inductive computation :: "'s \<Rightarrow> ('a list \<times> 'a list) \<times> ('b list \<times> 'b list) \<Rightarrow> 's \<Rightarrow> bool"
  ("_/\<leadsto>_/_" [64,64,64]63) where
  base[intro]: "q \<leadsto>(([], as'), ([], bs')) q"
| step_TT[intro]: "\<delta> q (Symb a, Symb b) = Some (q', True, True) \<Longrightarrow>
  q' \<leadsto>((as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>((a # as, as'), (b # bs, bs')) q''"
| step_TF[intro]: "\<delta> q (Symb a, safe_hd (bs @ bs')) = Some (q', True, False) \<Longrightarrow>
  q' \<leadsto>((as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>((a # as, as'), (bs, bs')) q''"
| step_FT[intro]: "\<delta> q (safe_hd (as @ as'), Symb b) = Some (q', False, True) \<Longrightarrow>
  q' \<leadsto>((as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>((as, as'), (b # bs, bs')) q''"

definition \<tau> :: "('a list \<times> 'b list) set" where
  "\<tau> = {(as, bs). \<exists>q. init \<leadsto>((as, []), (bs, [])) q \<and> accept q}"

lemma step_TF_rev: "q \<leadsto>((as, a # as'), (bs, bs')) q' \<Longrightarrow>
  \<delta> q' (Symb a, safe_hd bs') = Some (q'', True, False) \<Longrightarrow> q \<leadsto>((as @ [a], as'), (bs, bs')) q''"
  by (induction q "((as, a # as'), (bs, bs'))" q' arbitrary: as bs rule: computation.induct)
     (auto simp: safe_hd_def)

lemma step_FT_rev: "q \<leadsto>((as, as'), (bs, b' # bs')) q' \<Longrightarrow>
  \<delta> q' (safe_hd as', Symb b') = Some (q'', False, True) \<Longrightarrow> q \<leadsto>((as, as'), (bs @ [b'], bs')) q''"
  by (induction q "((as, as'), (bs, b' # bs'))" q' arbitrary: as bs rule: computation.induct)
     (auto simp: safe_hd_def)

lemma comp_unreachable:
  "q \<leadsto>((as, as'), (bs, bs')) q' \<Longrightarrow> (\<And>z. \<delta> q z = None) \<Longrightarrow> q = q'"
  by (auto elim: computation.cases)

lemma comp_closed: "q \<leadsto>((as, as'), (bs, bs')) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q"
  by (induction q "((as, as'), (bs, bs'))" q' arbitrary: as as' bs bs' rule: computation.induct)
     (auto dest: closed)

lemma no_computation_dest: "q \<leadsto>(([], as'), ([], bs')) q' \<Longrightarrow> q = q'"
  by (auto elim: computation.cases)

lemma comp_split: "q \<leadsto>((as @ as', as''), (bs, bs')) q' \<Longrightarrow>
  \<exists>q'' cs cs'. bs = cs @ cs' \<and> q \<leadsto>((as, as' @ as''), (cs, cs' @ bs')) q'' \<and>
    q'' \<leadsto>((as', as''), (cs', bs')) q'"
proof (induction q "((as @ as', as''), (bs, bs'))" q' arbitrary: as bs rule: computation.induct)
  case (step_TT q a b q' as' bs q'')
  then show ?case
  proof (cases as)
    case (Cons x xs)
    show ?thesis
      using step_TT(1,2,4) step_TT(3)[of xs]
      by (auto simp: Cons) (metis append_Cons computation.step_TT)
  qed fastforce
next
  case (step_TF q a bs q' as q'')
  then show ?case
    by (cases as) fastforce+
next
  case (step_FT q b q' bs q'')
  then show ?case
  proof (cases as)
    case (Cons x xs)
    then show ?thesis
      using step_FT
      by auto (metis Cons_eq_appendI computation.step_FT)
  qed fastforce
qed auto

lemma comp_pull: "q \<leadsto>((u1, u1'), (v1, v1')) q'' \<Longrightarrow> q \<leadsto>((u1 @ u2, u3), (v1 @ v2, v3)) q' \<Longrightarrow>
  safe_hd u1' = safe_hd (u2 @ u3) \<Longrightarrow> safe_hd v1' = safe_hd (v2 @ v3) \<Longrightarrow>
  q'' \<leadsto>((u2, u3), (v2, v3)) q'"
proof (induction q "((u1, u1'), (v1, v1'))" q'' arbitrary: u1 v1 rule: computation.induct)
  case (step_TT q a b q''' as bs q'')
  have "q''' \<leadsto>((as @ u2, u3), bs @ v2, v3) q'"
    using step_TT(1,4)
    by (auto simp: safe_hd_def elim: computation.cases)
  then show ?case
    by (rule step_TT(3)[OF _ step_TT(5,6)])
next
  case (step_TF q a bs q''' as q'')
  have "q''' \<leadsto>((as @ u2, u3), bs @ v2, v3) q'"
    using step_TF(1,4) safe_hd_Cons_app[of "bs @ v2" _ _ v3, simplified]
    by (auto simp: safe_hd_app'[OF step_TF(6)] safe_hd_Cons elim: computation.cases)
  then show ?case
    by (rule step_TF(3)[OF _ step_TF(5,6)])
next
  case (step_FT q as b q''' bs q'')
  have "q'''\<leadsto>((as @ u2, u3), bs @ v2, v3)q'"
    using step_FT(1,4) safe_hd_Cons_app[of "as @ u2" _ _ u3, simplified]
    by (auto simp: safe_hd_app'[OF step_FT(5)] safe_hd_Cons elim: computation.cases)
  then show ?case
    by (rule step_FT(3)[OF _ step_FT(5,6)])
qed auto

lemma comp_swap: "q \<leadsto>((as, a' # as'), (bs, bs')) q' \<Longrightarrow> q \<leadsto>((as, a' # as''), (bs, bs')) q'"
  by (induction q "((as, a' # as'), (bs, bs'))" q' arbitrary: as bs
      rule: computation.induct)
     (auto cong: safe_hd_app_Cons)

lemma comp_swap': "q \<leadsto>((as, as'), (bs, b' # bs')) q' \<Longrightarrow> q \<leadsto>((as, as'), (bs, b' # bs'')) q'"
  by (induction q "((as, as'), (bs, b' # bs'))" q' arbitrary: as bs
      rule: computation.induct)
    (auto cong: safe_hd_app_Cons)

lemma comp_swap_same_hd: "q \<leadsto>((as, as'), (bs, bs')) q' \<Longrightarrow>
  safe_hd as' = safe_hd as'' \<Longrightarrow> safe_hd bs' = safe_hd bs'' \<Longrightarrow>
  q \<leadsto>((as, as''), (bs, bs'')) q'"
  by (induction q "((as, as'), (bs, bs'))" q' arbitrary: as bs rule: computation.induct)
     (auto cong: safe_hd_app')

lemma comp_trans: "q \<leadsto>((as, as'), (bs, bs')) q' \<Longrightarrow> q' \<leadsto>((cs, cs'), (ds, ds')) q'' \<Longrightarrow>
  safe_hd as' = safe_hd (cs @ cs') \<Longrightarrow> safe_hd bs' = safe_hd (ds @ ds') \<Longrightarrow>
  q \<leadsto>((as @ cs, cs'), (bs @ ds, ds')) q''"
  apply (induction q "((as, as'), (bs, bs'))" q' arbitrary: as bs rule: computation.induct)
  using safe_hd_app'
  by (fastforce dest: safe_hd_Nil_dest)+

lemma comp_swapR: "q \<leadsto>(([], as'), (bs, bs')) q' \<Longrightarrow> q \<leadsto>(([], as'), (bs, cs')) q'"
  by (induction q "(([] :: 'a list, as'), (bs, bs'))" q' arbitrary: bs rule: computation.induct)
     (auto)

lemma comp_transR:
  assumes "q \<leadsto>(([], as'), (bs, bs')) q'" "q' \<leadsto>(([], as'), (cs, bs'')) q''"
  shows "q \<leadsto>(([], as'), (bs @ cs, bs'')) q''"
  using comp_trans[OF comp_swapR[OF assms(1)] assms(2)]
  by auto

lemma fst_stepL: "q\<leadsto>(([], as'), (b # bs, bs'))q' \<Longrightarrow>
  \<exists>q''. \<delta> q (safe_hd as', Symb b) = Some (q'', False, True) \<and> q'' \<leadsto>(([], as'), (bs, bs')) q'"
  by (auto elim: computation.cases)

lemma comp_splitL: "q\<leadsto>(([], as'), (cs @ cs', cs'')) q' \<Longrightarrow>
  \<exists>q''. q \<leadsto>(([], as'), (cs, cs' @ cs'')) q'' \<and> q'' \<leadsto>(([], as'), (cs', cs'')) q'"
  by (induction cs arbitrary: q) (fastforce dest!: fst_stepL)+

lemma shift_compL: assumes "r\<leadsto>(([], w), (cs @ cs'), ds')t" "t\<leadsto>((w, []), ds', [])r'"
  shows "\<exists>t''. r \<leadsto>(([], w), (cs, cs' @ ds')) t'' \<and> t'' \<leadsto>((w, []), (cs' @ ds', [])) r'"
proof -
  obtain t'' where t''_def: "r \<leadsto>(([], w), (cs, cs' @ ds')) t''" "t'' \<leadsto>(([], w), (cs', ds')) t"
    using comp_splitL[OF assms(1)]
    by auto
  have comb: "t'' \<leadsto>((w, []), (cs' @ ds', [])) r'"
    using comp_trans[OF t''_def(2) assms(2)]
    by auto
  show ?thesis
    using t''_def(1) comb
    by auto
qed

lemma fst_stepR: "q\<leadsto>((a # as, as'), ([], bs'))q' \<Longrightarrow>
  \<exists>q''. \<delta> q (Symb a, safe_hd bs') = Some (q'', True, False) \<and> q'' \<leadsto>((as, as'), ([], bs')) q'"
  by (auto elim: computation.cases)

inductive computation_ext ::
  "'s \<Rightarrow> 's list \<times> ('a list \<times> 'a list) \<times> ('b list \<times> 'b list) \<Rightarrow> 's \<Rightarrow> bool"
  ("_/\<leadsto>e_/_" [64,64,64]63) where
  base_ext[intro]: "q \<leadsto>e([], ([], as'), ([], bs')) q"
| step_TT_ext[intro]: "\<delta> q (Symb a, Symb b) = Some (q', True, True) \<Longrightarrow>
  q' \<leadsto>e(qs, (as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>e(q' # qs, (a # as, as'), (b # bs, bs')) q''"
| step_TF_ext[intro]: "\<delta> q (Symb a, safe_hd (bs @ bs')) = Some (q', True, False) \<Longrightarrow>
  q' \<leadsto>e(qs, (as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>e(q' # qs, (a # as, as'), (bs, bs')) q''"
| step_FT_ext[intro]: "\<delta> q (safe_hd (as @ as'), Symb b) = Some (q', False, True) \<Longrightarrow>
  q' \<leadsto>e(qs, (as, as'), (bs, bs')) q'' \<Longrightarrow> q \<leadsto>e(q' # qs, (as, as'), (b # bs, bs')) q''"

lemma comp_to_ext: "q \<leadsto>((as, as'), (bs, bs')) q' \<Longrightarrow>
  \<exists>qs. q \<leadsto>e(qs, (as, as'), (bs, bs')) q'"
  by (induction q "((as, as'), (bs, bs'))" q' arbitrary: as bs rule: computation.induct) auto

lemma ext_to_comp: "q \<leadsto>e(qs, (as, as'), (bs, bs')) q' \<Longrightarrow> q \<leadsto>((as, as'), (bs, bs')) q'"
  by (induction q "(qs, (as, as'), (bs, bs'))" q' arbitrary: qs as bs rule: computation_ext.induct)
     (auto)

lemma ext_closed: "q \<leadsto>e(qs, (as, as'), (bs, bs')) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> set qs \<subseteq> Q"
  apply (induction q "(qs, (as, as'), (bs, bs'))" q' arbitrary: qs as bs rule: computation_ext.induct)
  using closed
  by auto

lemma comp_ext_trans: "q \<leadsto>e(qs, (as, as'), (bs, bs')) q' \<Longrightarrow>
  q' \<leadsto>e(qs', (cs, cs'), (ds, ds')) q'' \<Longrightarrow>
  safe_hd as' = safe_hd (cs @ cs') \<Longrightarrow> safe_hd bs' = safe_hd (ds @ ds') \<Longrightarrow>
  q \<leadsto>e(qs @ qs', (as @ cs, cs'), (bs @ ds, ds')) q''"
  apply (induction q "(qs, (as, as'), (bs, bs'))" q' arbitrary: qs as bs rule: computation_ext.induct)
  using safe_hd_app'
  by (fastforce dest: safe_hd_Nil_dest)+

lemma comp_ext_swapR: "q \<leadsto>e(qs, ([], as'), (bs, bs')) q' \<Longrightarrow> q \<leadsto>e(qs, ([], as'), (bs, cs')) q'"
  by (induction q "(qs, ([] :: 'a list, as'), (bs, bs'))" q' arbitrary: qs bs rule: computation_ext.induct)
     (auto)

lemma comp_ext_transR:
  assumes "q \<leadsto>e(qs, ([], as'), (bs, bs')) q'" "q' \<leadsto>e(qs', ([], as'), (cs, bs'')) q''"
  shows "q \<leadsto>e(qs @ qs', ([], as'), (bs @ cs, bs'')) q''"
  using comp_ext_trans[OF comp_ext_swapR[OF assms(1)] assms(2)]
  by auto

lemma ext_split: "q \<leadsto>e(qs @ q' # qs', ([], as'), (bs @ b # bs', bs'')) q'' \<Longrightarrow>
  length qs = length bs \<Longrightarrow>
  q \<leadsto>e(qs @ [q'], ([], as'), (bs @ [b], bs' @ bs'')) q' \<and> q' \<leadsto>e(qs', ([], as'), (bs', bs'')) q''"
proof (induction q "(qs @ q' # qs',  ([] :: 'a list, as'), (bs @ b # bs', bs''))" q''
    arbitrary: qs bs rule: computation_ext.induct)
  case (step_FT_ext q b q'a qs bs q'' qsa bsa)
  then show ?case
    by (cases qsa; cases bsa) auto
qed simp

lemma ext_rem_loop:
  assumes "q \<leadsto>e(qs @ q' # qs' @ q' # qs'', ([], as'), (bs @ b # bs' @ b' # bs'', bs''')) q''"
    "length qs = length bs" "length qs' = length bs'"
  shows "q \<leadsto>e(qs @ q' # qs'', ([], as'), (bs @ b # bs'', bs''')) q''"
proof -
  have split: "q\<leadsto>e(qs @ [q'], ([], as'), bs @ [b], (bs' @ b' # bs'') @ bs''')q'"
    "q' \<leadsto>e(qs' @ q' # qs'', ([], as'), bs' @ b' # bs'', bs''')q''"
    using ext_split[OF assms(1,2)]
    by auto
  have split': "q'\<leadsto>e(qs' @ [q'], ([], as'), bs' @ [b'], bs'' @ bs''')q'"
    "q'\<leadsto>e(qs'', ([], as'), bs'', bs''')q''"
    using ext_split[OF split(2)] assms(3)
    by auto
  show ?thesis
    using comp_ext_transR[OF split(1) split'(2)]
    by auto
qed

end

locale oTDFA = TDFA init \<delta> accept Q
  for init :: "'s"
    and \<delta> :: "'s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('s \<times> bool \<times> bool) option"
    and accept :: "'s \<Rightarrow> bool"
    and Q :: "'s set" +
  assumes move_one: "\<delta> q (a, b) = Some (q', True, True) \<Longrightarrow> False"
begin

lemma comp_ext_length: "q \<leadsto>e(qs, (as, as'), (bs, bs')) q' \<Longrightarrow> length qs = length as + length bs"
  by (induction q "(qs, (as, as'), (bs, bs'))" q' arbitrary: qs as bs rule: computation_ext.induct)
     (auto dest: move_one)

lemma fst_step: "q \<leadsto>((a # as, as'), (b # bs, bs')) q' \<Longrightarrow>
  (\<exists>q''. \<delta> q (Symb a, Symb b) = Some (q'', True, False) \<and> q'' \<leadsto>((as, as'), (b # bs, bs')) q') \<or>
  (\<exists>q''. \<delta> q (Symb a, Symb b) = Some (q'', False, True) \<and> q'' \<leadsto>((a # as, as'), (bs, bs')) q')"
  by (auto simp: safe_hd_def dest: move_one elim: computation.cases)

lemma split_outs: "q \<leadsto>((a # as, as'), (bs, bs')) q' \<Longrightarrow>
  \<exists>r r' cs cs'. bs = cs @ cs' \<and> q \<leadsto>(([], a # as @ as'), (cs, cs' @ bs')) r \<and>
  \<delta> r (Symb a, safe_hd (cs' @ bs')) = Some (r', True, False) \<and> r' \<leadsto>((as, as'), (cs', bs')) q'"
proof (induction bs arbitrary: q)
  case Nil
  then show ?case
    using fst_stepR
    by auto
next
  case (Cons b bs'')
  show ?case
    using fst_step[OF Cons(2)]
  proof (rule disjE)
    assume "\<exists>q''. \<delta> q (Symb a, Symb b) = Some (q'', True, False) \<and>
      q''\<leadsto>((as, as'), b # bs'', bs')q'"
    then obtain r' where r'_def: "\<delta> q (Symb a, Symb b) = Some (r', True, False)"
      "r'\<leadsto>((as, as'), b # bs'', bs')q'"
      by auto
    show "\<exists>r r' cs cs'. b # bs'' = cs @ cs' \<and>
      q\<leadsto>(([], a # as @ as'), cs, cs' @ bs')r \<and>
      \<delta> r (Symb a, safe_hd (cs' @ bs')) = Some (r', True, False) \<and> r'\<leadsto>((as, as'), cs', bs')q'"
      apply (rule exI[of _ q])
      apply (rule exI[of _ r'])
      apply (rule exI[of _ "[]"])
      apply (auto simp: safe_hd_def r'_def)
      done
  next
    assume "\<exists>q''. \<delta> q (Symb a, Symb b) = Some (q'', False, True) \<and>
      q''\<leadsto>((a # as, as'), bs'', bs')q'"
    then obtain s where s_def: "\<delta> q (Symb a, Symb b) = Some (s, False, True)"
      "s\<leadsto>((a # as, as'), bs'', bs')q'"
      by auto
    obtain r r' cs cs' where split: "bs'' = cs @ cs'" "s\<leadsto>(([], a # as @ as'), cs, cs' @ bs')r"
      "\<delta> r (Symb a, safe_hd (cs' @ bs')) = Some (r', True, False)" "r'\<leadsto>((as, as'), cs', bs')q'"
      using Cons(1)[OF s_def(2)]
      by auto
    have comp_q_s: "q \<leadsto>(([], a # as @ as'), ([b], bs'' @ bs')) s"
      apply (rule step_FT[OF _ base])
      using s_def(1)
      by (auto simp: safe_hd_def)
    have comp_q_r: "q \<leadsto>(([], a # as @ as'), (b # cs, cs' @ bs')) r"
      using split(2) comp_trans[OF comp_q_s] comp_q_s
      by (auto simp: split(1) split: list.splits)
    show "\<exists>r r' cs cs'. b # bs'' = cs @ cs' \<and> q\<leadsto>(([], a # as @ as'), cs, cs' @ bs')r \<and>
      \<delta> r (Symb a, safe_hd (cs' @ bs')) = Some (r', True, False) \<and> r'\<leadsto>((as, as'), cs', bs')q'"
      apply (rule exI[of _ r])
      apply (rule exI[of _ r'])
      apply (rule exI[of _ "b # cs"])
      apply (rule exI[of _ cs'])
      apply (auto simp: split comp_q_r)
      done
  qed
qed

lemma set_zip_upd: "length xs = length ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> \<exists>x'. g x' y) \<Longrightarrow>
  \<exists>xs'. length xs' = length ys \<and> (\<forall>(x', y) \<in> set (zip xs' ys). g x' y)"
proof (induction xs ys rule: list_induct2)
  case (Cons x xs y ys)
  obtain x' where x'_def: "g x' y"
    using Cons(3)
    by auto
  obtain xs' where xs'_def: "length xs' = length ys" "\<forall>(x', y) \<in> set (zip xs' ys). g x' y"
    using Cons(2,3)
    by auto
  show ?case
    using x'_def xs'_def
    by (auto intro!: exI[of _ "x' # xs'"])
qed auto

lemma set_zip_upd4:
  assumes "length xs = length ys"
  shows "(\<And>x y z w. (x, y, z, w) \<in> set (zip xs ys) \<Longrightarrow> \<exists>x'. g x' y z w) \<Longrightarrow>
    \<exists>xs'. length xs' = length ys \<and> (\<forall>(x', y, z, w) \<in> set (zip xs' ys). g x' y z w)"
  using set_zip_upd[OF assms, of "\<lambda>x' y. case y of (y', z, w) \<Rightarrow> g x' y' z w"]
  by auto

lemma split_outss:
  assumes "\<And>w r r'. (w, r, r') \<in> set ws \<Longrightarrow> r \<leadsto>((w, []), (u, [])) r'"
  shows "\<exists>cs cs' ts. u = cs @ cs' \<and> length ts = length ws \<and>
    (\<forall>(t, w, r, r') \<in> set (zip ts ws). r \<leadsto>(([], w), (cs, cs')) t \<and> t \<leadsto>((w, []), (cs', [])) r') \<and>
    (case concat (map fst ws) of [] \<Rightarrow> cs' = [] | _ \<Rightarrow> \<exists>a \<in> set (zip ts ws).
      case a of (t, w, r, r') \<Rightarrow> \<exists>t'. \<delta> t (safe_hd w, safe_hd cs') = Some (t', True, False))"
  using assms
proof (induction ws)
  case (Cons wrr' ws)
  obtain w r r' where wrr'_def: "wrr' = (w, r, r')"
    by (cases wrr') auto
  obtain cs cs' ts where ws_def: "u = cs @ cs'" "length ts = length ws"
    "\<And>t w r r'. (t, w, r, r') \<in> set (zip ts ws) \<Longrightarrow>
      r \<leadsto>(([], w), (cs, cs')) t \<and> t \<leadsto>((w, []), (cs', [])) r'"
    "(case concat (map fst ws) of [] \<Rightarrow> cs' = [] | _ \<Rightarrow> \<exists>a \<in> set (zip ts ws).
      case a of (t, w, r, r') \<Rightarrow> \<exists>t'. \<delta> t (safe_hd w, safe_hd cs') = Some (t', True, False))"
    using Cons
    by (auto split: prod.splits)
  have comp: "r \<leadsto>((w, []), (u, [])) r'"
    using Cons(2)
    by (auto simp: wrr'_def)
  show ?case
  proof (cases w)
    case Nil
    obtain t where t_def: "r\<leadsto>(([], []), cs, cs')t" "t\<leadsto>(([], []), cs', [])r'"
      using comp_splitL[OF comp[unfolded Nil ws_def(1)]] ws_def
      by auto
    have concat_map_fst_Nil: "(\<forall>x \<in> set ws. fst x = []) \<Longrightarrow> concat (map fst ws) = []"
      by auto
    have one_step: "case concat (map fst (wrr' # ws)) of [] \<Rightarrow> cs' = []
      | _ \<Rightarrow> \<exists>a \<in> set (zip (t # ts) (wrr' # ws)).
        case a of (t, w, r, r') \<Rightarrow> \<exists>t'. \<delta> t (safe_hd w, safe_hd cs') = Some (t', True, False)"
      using ws_def(4)
      by (auto simp: wrr'_def Nil dest: concat_map_fst_Nil split: list.splits)
    show ?thesis
      apply (rule exI[of _ cs])
      apply (rule exI[of _ cs'])
      using ws_def(1,2,3) t_def one_step
      by (auto simp: wrr'_def Nil intro!: exI[of _ "t # ts"])
  next
    case (Cons a as)
    obtain t t' ds ds' where split: "u = ds @ ds'" "r\<leadsto>(([], a # as), ds, ds')t"
      "\<delta> t (Symb a, safe_hd ds') = Some (t', True, False)" "t'\<leadsto>((as, []), ds', [])r'"
      "t\<leadsto>((a # as, []), ds', [])r'"
      using split_outs[OF comp[unfolded Cons]]
      by fastforce
    show ?thesis
    proof (cases "length ds \<le> length cs")
      case True
      obtain cs'' where cs''_def: "cs = ds @ cs''"
        using ws_def(1) split(1) True split_app[of ds ds' cs cs']
        by auto
      have ds'_def: "ds' = cs'' @ cs'"
        using ws_def(1)[unfolded split(1) cs''_def]
        by auto
      have ts_ts': "\<And>t w r r'. (t, w, r, r') \<in> set (zip ts ws) \<Longrightarrow>
        \<exists>t''. r \<leadsto>(([], w), (ds, ds')) t'' \<and> t'' \<leadsto>((w, []), (ds', [])) r'"
        using ws_def(3) shift_compL[of _ _ ds cs'' cs', folded cs''_def ds'_def]
        by fastforce
      obtain ts' where ts'_def: "length ts' = length ts"
        "\<And>t w r r'. (t, w, r, r') \<in> set (zip ts' ws) \<Longrightarrow>
          r \<leadsto>(([], w), (ds, ds')) t \<and> t \<leadsto>((w, []), (ds', [])) r'"
        using set_zip_upd4[OF ws_def(2) ts_ts'] ws_def(2)
        by fastforce
      show ?thesis
        apply (rule exI[of _ ds])
        apply (rule exI[of _ ds'])
        using split(1) ts'_def(1) ws_def(2) split(2,3,5) ts'_def(2)
        by (auto simp: wrr'_def Cons safe_hd_Cons intro!: exI[of _ "t # ts'"])
    next
      case False
      obtain ds'' where ds''_def: "ds = cs @ ds''"
        using ws_def(1) split(1) False split_app[of cs cs' ds ds']
        by auto
      have cs'_def: "cs' = ds'' @ ds'"
        using ws_def(1)[unfolded split(1) ds''_def]
        by auto
      obtain t' where t'_def: "r \<leadsto>(([], a # as), (cs, cs')) t'"
        "t' \<leadsto>((a # as, []), (cs', [])) r'"
        using shift_compL[OF split(2)[unfolded ds''_def] split(5)]
        by (auto simp: cs'_def)
      have concat_map_fst_Cons: "concat (map fst ws) \<noteq> []"
        using False cs'_def ds''_def ws_def(4)
        by force
      show ?thesis
        apply (rule exI[of _ cs])
        apply (rule exI[of _ cs'])
        using ws_def t'_def concat_map_fst_Cons
        by (fastforce simp: wrr'_def Cons intro!: exI[of _ "t' # ts"] split: list.splits)
    qed
  qed
qed auto

lemma first_reaches:
  assumes "q \<leadsto>((us @ us', us''), (vs @ vs', vs'')) q'" "us \<noteq> [] \<or> vs \<noteq> []"
  shows "(\<exists>ws ws' q''. vs = ws @ ws' \<and> ws' \<noteq> [] \<and>
      q \<leadsto>((us, us' @ us''), (ws, ws' @ vs' @ vs'')) q'' \<and>
      q'' \<leadsto>((us', us''), (ws' @ vs', vs'')) q') \<or>
    (\<exists>ws ws' q''. us = ws @ ws' \<and> ws' \<noteq> [] \<and>
      q \<leadsto>((ws, ws' @ us' @ us''), (vs, vs' @ vs'')) q'' \<and>
      q'' \<leadsto>((ws' @ us', us''), (vs', vs'')) q')"
  using assms
proof (induction "length us + length vs" arbitrary: q us vs rule: nat_less_induct)
  case 1
  then have IH: "\<And>uss vss q. q \<leadsto>((uss @ us', us''), (vss @ vs', vs'')) q' \<Longrightarrow>
    (uss \<noteq> [] \<or> vss \<noteq> []) \<Longrightarrow> length uss + length vss < length us + length vs \<Longrightarrow>
    (\<exists>ws ws' q''. vss = ws @ ws' \<and> ws' \<noteq> [] \<and>
      q \<leadsto>((uss, us' @ us''), (ws, ws' @ vs' @ vs'')) q'' \<and>
      q'' \<leadsto>((us', us''), (ws' @ vs', vs'')) q') \<or>
    (\<exists>ws ws' q''. uss = ws @ ws' \<and> ws' \<noteq> [] \<and>
      q \<leadsto>((ws, ws' @ us' @ us''), (vss, vs' @ vs'')) q'' \<and>
      q'' \<leadsto>((ws' @ us', us''), (vs', vs'')) q')"
    by auto
  show ?case
  proof (cases us)
    case Nil
    show ?thesis
      apply (rule disjI1)
      apply (rule exI[of _ "[]"])
      using 1(2,3)
      by (auto simp: Nil)
  next
    case u_def: (Cons u uss')
    show ?thesis
    proof (cases vs)
      case Nil
      show ?thesis
        apply (rule disjI2)
        apply (rule exI[of _ "[]"])
        using 1(2)
        by (auto simp: u_def Nil)
    next
      case v_def: (Cons v vss')
      have assm: "uss' \<noteq> [] \<or> vs \<noteq> []" "us \<noteq> [] \<or> vss' \<noteq> []"
        by (auto simp: u_def v_def)
      obtain qm where step:
        "(\<delta> q (Symb u, Symb v) = Some (qm, True, False) \<and>
          qm \<leadsto>((uss' @ us', us''), (vs @ vs', vs'')) q') \<or>
        (\<delta> q (Symb u, Symb v) = Some (qm, False, True) \<and>
          qm \<leadsto>((us @ us', us''), (vss' @ vs', vs'')) q')"
        using fst_step[OF 1(2)[unfolded u_def v_def, simplified]]
        by (auto simp: u_def v_def)
      then show ?thesis
      proof (rule disjE)
        assume "\<delta> q (Symb u, Symb v) = Some (qm, True, False) \<and>
          qm \<leadsto>((uss' @ us', us''), (vs @ vs', vs'')) q'"
        then have lassms: "\<delta> q (Symb u, Symb v) = Some (qm, True, False)"
          "qm \<leadsto>((uss' @ us', us''), (vs @ vs', vs'')) q'"
          by auto
        show "(\<exists>ws ws' q''. vs = ws @ ws' \<and> ws' \<noteq> [] \<and>
            q\<leadsto>((us, us' @ us''), ws, ws' @ vs' @ vs'')q'' \<and>
            q''\<leadsto>((us', us''), ws' @ vs', vs'')q') \<or>
          (\<exists>ws ws' q''. us = ws @ ws' \<and> ws' \<noteq> [] \<and>
            q\<leadsto>((ws, ws' @ us' @ us''), vs, vs' @ vs'')q'' \<and>
            q''\<leadsto>((ws' @ us', us''), vs', vs'')q')"
          using IH[OF lassms(2) assm(1), unfolded u_def, simplified]
          apply (rule disjE)
          subgoal
            apply (rule disjI1)
            using lassms(1)
            apply auto
            subgoal for ws ws' q''
              apply (rule exI[of _ ws])
              apply (rule exI[of _ ws'])
              apply (auto simp: u_def intro!: exI[of _ q''])
              apply (rule step_TF)
               apply (auto simp: v_def safe_hd_def split: list.splits)
              apply (metis append_Cons append_assoc list.inject)
              done
            done
          subgoal
            apply (rule disjI2)
            using lassms(1)
            apply (auto simp: u_def)
            subgoal for ws ws' q''
              apply (rule exI[of _ "u # ws"])
              apply (rule exI[of _ ws'])
              apply (auto simp: u_def v_def safe_hd_def intro!: exI[of _ q''])
              done
            done
          done
      next
        assume "\<delta> q (Symb u, Symb v) = Some (qm, False, True) \<and>
          qm\<leadsto>((us @ us', us''), vss' @ vs', vs'')q'"
        then have lassms: "\<delta> q (Symb u, Symb v) = Some (qm, False, True)"
          "qm\<leadsto>((us @ us', us''), vss' @ vs', vs'')q'"
          by auto
        show "(\<exists>ws ws' q''. vs = ws @ ws' \<and> ws' \<noteq> [] \<and>
            q\<leadsto>((us, us' @ us''), ws, ws' @ vs' @ vs'')q'' \<and>
            q''\<leadsto>((us', us''), ws' @ vs', vs'')q') \<or>
          (\<exists>ws ws' q''. us = ws @ ws' \<and> ws' \<noteq> [] \<and>
            q\<leadsto>((ws, ws' @ us' @ us''), vs, vs' @ vs'')q'' \<and>
            q''\<leadsto>((ws' @ us', us''), vs', vs'')q')"
          using IH[OF lassms(2) assm(2), unfolded v_def, simplified]
          apply (rule disjE)
          subgoal
            apply (rule disjI1)
            using lassms(1)
            apply auto
            subgoal for ws ws' q''
              apply (rule exI[of _ "v # ws"])
              apply (rule exI[of _ ws'])
              apply (auto simp: u_def v_def safe_hd_def intro!: exI[of _ q''])
              done
            done
          subgoal
            apply (rule disjI2)
            using lassms(1)
            apply (auto simp: u_def)
            subgoal for ws ws' q''
              apply (rule exI[of _ ws])
              apply (rule exI[of _ ws'])
              apply (auto simp: v_def intro!: exI[of _ q''])
              apply (rule step_FT)
               apply (auto simp: safe_hd_def split: list.splits)
              apply (metis append_Cons append_assoc list.inject)
              done
            done
          done
      qed
    qed
  qed
qed

lemma comp_to_states:
  assumes "q \<leadsto>(([], as'), (bs, bs')) q'" "q \<in> Q"
  shows "\<exists>qs. length qs = Suc (length bs) \<and> qs ! 0 = q \<and>
  (qs ! (length bs)) \<leadsto>(([], as'), ([], bs')) q' \<and> set qs \<subseteq> Q \<and>
  (\<forall>i < length bs. \<delta> (qs ! i) (safe_hd as', Symb (bs ! i)) = Some (qs ! (Suc i), False, True))"
  using assms
proof (induction bs arbitrary: q)
  case Nil
  then show ?case
    by (auto intro: exI[of _ "[q]"])
next
  case (Cons b bs'')
  obtain q'' where q''_def: "\<delta> q (safe_hd as', Symb b) = Some (q'', False, True)"
    "q'' \<leadsto>(([], as'), (bs'', bs')) q'"
    using fst_stepL[OF Cons(2)]
    by auto
  note q''_Q = closed[OF Cons(3) q''_def(1)]
  obtain qs where qs_def: "length qs = Suc (length bs'')"
    "qs ! 0 = q''" "(qs ! length bs'') \<leadsto>(([], as'), ([], bs')) q'" "set qs \<subseteq> Q"
    "\<And>i. i < length bs'' \<Longrightarrow>
      \<delta> (qs ! i) (safe_hd as', Symb (bs'' ! i)) = Some (qs ! Suc i, False, True)"
    using Cons(1)[OF q''_def(2) q''_Q]
    by auto
  show ?case
    apply (rule exI[of _ "q # qs"])
    using qs_def q''_def(1) Cons(3)
    apply auto
    subgoal for i
      by (cases i) auto
    done
qed

lemma states_to_comp:
  assumes "length qs = Suc (length bs) \<and> qs ! 0 = q \<and> qs ! (length bs) = q' \<and> (\<forall>i < length bs.
    \<delta> (qs ! i) (safe_hd as', Symb (bs ! i)) = Some (qs ! (Suc i), False, True))"
  shows "q \<leadsto>(([], as'), (bs, bs')) q'"
  using assms
proof (induction bs arbitrary: qs q' bs' rule: rev_induct)
  case (snoc b bs'')
  obtain qs'' q'' where split: "qs = qs'' @ [q'']" "length qs'' = Suc (length bs'')"
    using snoc(2)
    by (cases qs rule: rev_cases) auto
  have "q \<leadsto>(([], as'), (bs'', b # bs')) (qs ! (length bs''))"
    using snoc(1)[of qs''] snoc(2)
    by (auto simp: split nth_append split: if_splits)
  moreover have "\<delta> (qs ! (length bs'')) (safe_hd as', Symb b) = Some (q', False, True)"
    using snoc(2)
    by auto
  ultimately show ?case
    by (auto intro: step_FT_rev)
qed auto

lemma det_comp: "q\<leadsto>((u0, u @ u''), (v0 @ x, x'))r \<Longrightarrow> q\<leadsto>((u0 @ u, u''), v0 @ v, v')nr' \<Longrightarrow>
  \<exists>w w' nr. v = w @ w' \<and> q\<leadsto>((u0, u @ u''), v0 @ w, w' @ v')nr \<and> nr\<leadsto>((u, u''), (w', v'))nr'"
proof (induction q "((u0, u @ u''), (v0 @ x, x'))" r arbitrary: u0 v0 rule: computation.induct)
  case (step_TT q a b q' as bs q'')
  then show ?case
    using move_one
    by fastforce
next
  case (step_TF q a q' as q'')
  show ?case
  proof (cases v0)
    case Nil
    show ?thesis
      using comp_split[OF step_TF(4)]
      by (auto simp: Nil)
  next
    case (Cons b v0')
    have step: "\<delta> q (Symb a, safe_hd ((v0 @ v) @ v')) = Some (q', True, False)"
      using step_TF(1)
      by (auto simp: Cons safe_hd_Cons)
    have det_comp: "q'\<leadsto>((as @ u, u''), v0 @ v, v')nr'"
      apply (rule computation.cases[OF step_TF(4)])
      using step
      by (auto simp: safe_hd_Cons)
    show ?thesis
      using step_TF(3)[OF det_comp] step
      by (fastforce simp: Cons)
  qed
next
  case (step_FT q a b q' v0' r')
  show ?case
  proof (cases v0)
    case Nil
    show ?thesis
      using comp_split[OF step_FT(5)]
      by (auto simp: Nil)
  next
    case (Cons b' v0'')
    have v0'_def: "v0' = v0'' @ x"
      using step_FT(4)
      by (auto simp: Cons)
    have step: "\<delta> q (safe_hd (a @ u @ u''), Symb b') = Some (q', False, True)"
      using step_FT(1,4)
      by (auto simp: Cons)
    have det_comp: "q'\<leadsto>((a @ u, u''), v0'' @ v, v')nr'"
      apply (rule computation.cases[OF step_FT(5)])
      using step move_one
         apply (auto simp: Cons safe_hd_Cons)
      apply (metis append.assoc option.inject prod.inject safe_hd_Cons_app)
      done
    show ?thesis
      using step_FT(3)[OF v0'_def det_comp] step
      by (auto simp: Cons)
  qed
qed auto

lemma det_comp_safe: "init\<leadsto>((u0 @ u, u''), v0 @ v, v')nr' \<Longrightarrow> init\<leadsto>((u0, u'), (v0 @ x, x'))r \<Longrightarrow>
  safe_hd (u @ u'') = safe_hd u' \<Longrightarrow>
  \<exists>w w' nr. v = w @ w' \<and> init\<leadsto>((u0, u @ u''), v0 @ w, w' @ v')nr \<and> nr\<leadsto>((u, u''), (w', v'))nr'"
  apply (rule det_comp)
  apply (rule comp_swap_same_hd)
    apply auto
  done

end

type_synonym 's otdfa_s = "'s + 's"

context TDFA
begin

definition otdfa_init :: "'s otdfa_s" where
  "otdfa_init = Inl init"

fun otdfa_delta :: "'s otdfa_s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('s otdfa_s \<times> bool \<times> bool) option" where
  "otdfa_delta (Inl q) (a, b) = (case \<delta> q (a, b) of Some (q', b1, b2) \<Rightarrow>
    if b1 \<and> b2 then Some (Inr q', True, False) else Some (Inl q', b1, b2)
  | _ \<Rightarrow> None)"
| "otdfa_delta (Inr q) (a, Symb b) = Some (Inl q, False, True)"
| "otdfa_delta (Inr q) (a, Blank) = None"

lemma otdfa_delta_Inr: "otdfa_delta q z = Some (Inr q', b1, b2) \<Longrightarrow>
  \<exists>q''. q = Inl q'' \<and> \<delta> q'' z = Some (q', True, True) \<and> b1 \<and> \<not>b2"
  by (induction q z rule: otdfa_delta.induct) (auto split: option.splits if_splits)

definition otdfa_accept :: "'s otdfa_s \<Rightarrow> bool" where
  "otdfa_accept q = (case q of Inl q' \<Rightarrow> accept q' | _ \<Rightarrow> False)"

definition otdfa_Q :: "'s otdfa_s set" where
  "otdfa_Q = Inl ` Q \<union> Inr ` Q"

lemma otdfa_finite_Q: "finite otdfa_Q"
  using finite_Q
  by (auto simp add: otdfa_Q_def)

lemma otdfa_init_in_Q: "otdfa_init \<in> otdfa_Q"
  using init_in_Q
  by (auto simp add: otdfa_init_def otdfa_Q_def)

lemma otdfa_closed:
  assumes "otdfa_delta q z = Some (q', b1, b2)" "q \<in> otdfa_Q"
  shows "q' \<in> otdfa_Q"
  using assms
  by (induction q z rule: otdfa_delta.induct)
     (auto simp: otdfa_Q_def split: option.splits prod.splits if_splits Al.splits dest: closed)

lemma otdfa_move_left:
  assumes "otdfa_delta q (a, b) = Some (q', True, b2)"
  shows "a \<noteq> Blank"
  using assms move_left
  by (induction q "(a, b)" rule: otdfa_delta.induct)
     (auto split: option.splits prod.splits if_splits Al.splits)

lemma otdfa_move_right:
  assumes "otdfa_delta q (a, b) = Some (q', b1, True)"
  shows "b \<noteq> Blank"
  using assms move_right
  by (induction q "(a, b)" rule: otdfa_delta.induct)
     (auto split: option.splits prod.splits if_splits Al.splits)

lemma otdfa_no_step:
  assumes "otdfa_delta q (a, b) = Some (q', False, False)"
  shows "False"
  using assms no_step
  by (induction q "(a, b)" rule: otdfa_delta.induct)
     (auto split: option.splits prod.splits if_splits Al.splits)

lemma otdfa_move_one:
  assumes "otdfa_delta q (a, b) = Some (q', True, True)"
  shows "False"
  using assms
  by (induction q "(a, b)" rule: otdfa_delta.induct)
     (auto split: option.splits prod.splits if_splits Al.splits)

interpretation otdfa: oTDFA otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using otdfa_finite_Q otdfa_init_in_Q otdfa_closed[rotated]
        otdfa_move_left otdfa_move_right otdfa_no_step otdfa_move_one
  apply unfold_locales
        apply auto[6]
   apply fastforce+
  done

lemma tdfa_comp_otdfa:
  assumes "q \<leadsto>((as, as'), (bs, bs')) q'"
  shows "otdfa.computation (Inl q) ((as, as'), (bs, bs')) (Inl q')"
  using assms
proof (induction q "((as, as'), (bs, bs'))" q' arbitrary: as as' bs bs' rule: computation.induct)
  case (step_TT q a b q' as as' bs bs' q'')
  show ?case
    by (rule otdfa.computation.intros(3)[rotated, OF otdfa.computation.intros(4),
        rotated, OF step_TT(3)])
       (auto simp: safe_hd_def step_TT(1))
qed auto

lemma otdfa_comp_tdfa:
  assumes "otdfa.computation r ((as, as'), (bs, bs')) (Inl q')"
    "r = Inl q \<or> (r = Inr q'' \<and> \<delta> q (Symb a, safe_hd (bs @ bs')) = Some (q'', True, True))"
  shows "q \<leadsto>(if r = Inr q'' then (a # as, as') else (as, as'), (bs, bs')) q'"
  using assms
proof (induction r "((as, as'), (bs, bs'))" "Inl q' :: 's otdfa_s" arbitrary: q as bs q' a q''
  rule: otdfa.computation.induct)
  case base
  then show ?case
    by auto
next
  case (step_TT r x b r' as bs)
  show ?case
    using otdfa_move_one[OF step_TT(1)]
    by auto
next
  case (step_TF r x bs r' as)
  show ?case
  proof (cases r')
    case (Inl r'')
    show ?thesis
      using step_TF
      by (fastforce simp: safe_hd_def Inl split: option.splits if_splits list.splits)
  next
    case (Inr r'')
    show ?thesis
      using step_TF
      by (auto simp: safe_hd_def Inr split: option.splits if_splits list.splits)
  qed
next
  case (step_FT r as b r' bs)
  then show ?case
    by (fastforce simp: safe_hd_def split: option.splits if_splits)
qed

lemma tdfa_otdfa_comp: "q \<leadsto>((as, as'), (bs, bs')) q' \<longleftrightarrow>
  otdfa.computation (Inl q) ((as, as'), (bs, bs')) (Inl q')"
  using tdfa_comp_otdfa otdfa_comp_tdfa[of "Inl q"]
  by auto

lemma tdfa_equiv_otdfa: "\<tau> = otdfa.\<tau>"
  unfolding \<tau>_def otdfa.\<tau>_def
  unfolding otdfa_init_def otdfa_accept_def tdfa_otdfa_comp
  by auto (auto split: sum.splits)

end

locale kTDFA = TDFA init \<delta> accept Q
  for init :: "'s"
    and \<delta> :: "'s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('s \<times> bool \<times> bool) option"
    and accept :: "'s \<Rightarrow> bool"
    and Q :: "'s set" +
  fixes kv :: nat
  assumes kval: "finite {bs. (as, bs) \<in> \<tau>}" "card {bs. (as, bs) \<in> \<tau>} \<le> kv"

lemma distinct_conv_nth': "distinct xs = (\<forall>i < size xs. \<forall>j < size xs. i < j \<longrightarrow> xs ! i \<noteq> xs ! j)"
  by (auto simp: distinct_conv_nth) (metis nat_neq_iff)

lemma length_concat_replicate:
  "length (concat (replicate n xs)) = n * length xs"
  by (induction n) auto

locale koTDFA = oTDFA init \<delta> accept Q + kTDFA init \<delta> accept Q kv
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a Al \<times> 'b Al \<Rightarrow> ('s \<times> bool \<times> bool) option"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set"
  and kv :: nat
begin

lemma loop:
  assumes "init \<leadsto>((as, us), (bs, vs @ vs')) q" "q \<leadsto>(([], us), (vs, vs')) q"
    "q \<leadsto>((us, []), (vs', [])) qf" "accept qf" "vs \<noteq> []"
  shows "False"
proof -
  define C where "C = {bs. (as @ us, bs) \<in> \<tau>}"
  have finite_C: "finite C"
    using kval
    by (auto simp: C_def)
  have comp: "\<And>n. q \<leadsto>(([], us), (concat (replicate n vs), vs')) q"
    subgoal for n
    proof (induction n)
      case (Suc n)
      show ?case
        using comp_transR[OF assms(2) Suc] assms(2)
        by fastforce
    qed auto
    done
  have safe_hd_concat: "\<And>n. n \<noteq> 0 \<Longrightarrow>
    safe_hd (vs @ vs') = safe_hd (concat (replicate n vs) @ vs')"
    using assms(5)
    apply (cases vs)
     apply (auto simp: safe_hd_def split: list.splits)
    apply (smt Suc_pred append_Cons concat.simps(2) list.inject replicate_Suc)
    done
  have "\<And>n. n \<noteq> 0 \<Longrightarrow> init \<leadsto>((as @ us, []), bs @ concat (replicate n vs) @ vs', []) qf"
    using comp_trans[OF comp_trans[OF assms(1) comp, OF _ safe_hd_concat] assms(3)] assms(5)
    by fastforce
  then have in_C: "\<And>n. n \<noteq> 0 \<Longrightarrow> bs @ concat (replicate n vs) @ vs' \<in> C"
    using assms(4,5)
    by (auto simp: \<tau>_def C_def)
  define f where "f = (\<lambda>n. bs @ concat (replicate n vs) @ vs')"
  have inj: "inj f"
    apply (auto simp: inj_def f_def)
    apply (drule arg_cong[of _ _ length])
    using assms(5)
    by (auto simp: length_concat_replicate)
  have "Suc kv = card (f ` {Suc 0..<Suc (Suc kv)})"
    using card_vimage_inj[OF inj, of "f ` {1..<Suc (Suc kv)}"] inj
    by (auto simp: inj_vimage_image_eq[OF inj])
  moreover have "\<dots> \<le> card C"
    apply (rule card_mono[OF finite_C])
    using in_C
    by (auto simp: f_def)
  finally show False
    using kval(2)[of "as @ us", folded C_def]
    by auto
qed

lemma state_bounded:
  assumes "init \<leadsto>((as, us), (bs, vs @ vs')) q" "q \<leadsto>(([], us), (vs, vs')) q'"
    "q' \<leadsto>((us, []), (vs', [])) qf" "accept qf"
  shows "length vs \<le> card Q"
proof (rule ccontr)
  assume "\<not>length vs \<le> card Q"
  then have len_vs: "length vs \<ge> Suc (card Q)"
    by auto
  then have vs_not_Nil: "vs \<noteq> []"
    by (cases vs) auto
  note q_Q = comp_closed[OF assms(1) init_in_Q]
  obtain qs where qs_def: "length qs = Suc (length vs)"
    "qs ! 0 = q" "(qs ! length vs) \<leadsto>(([], us), ([], vs')) q'" "set qs \<subseteq> Q"
    "\<And>i. i < length vs \<Longrightarrow> \<delta> (qs ! i) (safe_hd us, Symb (vs ! i)) = Some (qs ! Suc i, False, True)"
    using comp_to_states[OF assms(2) q_Q]
    by auto
  obtain qs'' q'' where qs_split: "qs = qs'' @ [q'']"
    using qs_def(1)
    by (cases qs rule: rev_cases) auto
  have set_qs'': "set qs'' \<subseteq> Q"
    using qs_def(4)
    by (auto simp: qs_split)
  note card_set_qs = card_mono[OF finite_Q set_qs'']
  have "length qs'' \<ge> Suc (card (set qs''))"
    using card_set_qs len_vs qs_def(1)
    by (auto simp: qs_split)
  then obtain i j where "i < j" "j < length qs''" "qs'' ! i = qs'' ! j"
    using distinct_card[of qs'']
    by (auto simp: distinct_conv_nth')
  then have ij_def: "i < j" "Suc j < length qs" "qs ! i = qs ! j"
    by (auto simp: qs_def(1) qs_split nth_append)
  have take_drop_i: "take i vs @ drop i vs = vs"
    "take (j - i) (drop i vs) @ drop j vs = drop i vs"
    using ij_def
    by (auto simp: qs_def(1))
       (smt append.assoc append_take_drop_id le_add_diff_inverse less_imp_le_nat same_append_eq
        take_add)
  define r where "r = qs ! i"
  have min_vs_i_j_i: "min (length vs - i) (j - i) = j - i"
    using ij_def
    by (auto simp: min_def qs_def(1))
  have comp_q_r: "q \<leadsto>(([], us), (take i vs, drop i vs @ vs')) r"
    apply (rule states_to_comp[of "take (Suc i) qs"])
    using ij_def qs_def(5)
    by (auto simp: qs_def(1,2) r_def) linarith
  then have comp_init_r: "init \<leadsto>((as, us), bs @ take i vs, drop i vs @ vs') r"
    using comp_trans[OF assms(1) comp_q_r]
    by (auto simp: take_drop_i append.assoc[symmetric])
  have comp_r_r: "r \<leadsto>(([], us), (take (j - i) (drop i vs), drop j vs @ vs')) r"
    apply (rule states_to_comp[of "take (Suc (j - i)) (drop i qs)"])
    using ij_def qs_def(5)
    by (auto simp: r_def qs_def(1) min_vs_i_j_i)
  have comp_r_q': "r \<leadsto>(([], us), (drop j vs, vs')) q'"
    apply (rule comp_trans[OF states_to_comp[of "drop j qs"] qs_def(3), simplified])
    using ij_def qs_def(5)
    by (auto simp: r_def qs_def(1))
  have comp_r_qf: "r \<leadsto>((us, []), drop j vs @ vs', []) qf"
    using comp_trans[OF comp_r_q' assms(3)]
    by auto
  have "drop j vs @ vs' \<noteq> []"
    using ij_def
    by (auto simp: qs_def(1))
  then show "False"
    using loop[OF _ comp_r_r comp_r_qf assms(4)] comp_init_r ij_def
    by (auto simp: append.assoc[symmetric] take_drop_i qs_def(1))
qed

lemma lin_bounded: "init \<leadsto>((as, us), (bs, vs)) q \<Longrightarrow> q \<leadsto>((us, []), (vs, [])) qf \<Longrightarrow>
  accept qf \<Longrightarrow> length vs \<le> (length us + 1) * card Q"
proof (induction us arbitrary: as bs vs q)
  case Nil
  then show ?case
    using state_bounded[OF _ _ base]
    by auto
next
  case (Cons u us')
  obtain r r' cs cs' where split: "vs = cs @ cs'" "q\<leadsto>(([], u # us' @ []), cs, cs' @ [])r"
    "\<delta> r (Symb u, safe_hd (cs' @ [])) = Some (r', True, False)" "r'\<leadsto>((us', []), cs', [])qf"
    using split_outs[OF Cons(3)]
    by auto
  have split': "q\<leadsto>(([], u # us'), cs, cs')r"
    using split(2)
    by (cases cs) auto
  have init_ext: "init\<leadsto>((as @ [u], us'), bs @ cs, cs')r'"
    using comp_trans[OF Cons(2) split'] split(2,3)
    by (auto simp: split(1) safe_hd_def intro: step_TF_rev split: list.splits)
  have comp_r_qf: "r\<leadsto>((u # us', []), cs', [])qf"
    using comp_trans[OF _ split(4) _ refl, of r "[u]" us' "[]"]
      step_TF[OF _ base, simplified, OF split(3)[simplified]]
    by auto
  show ?case
    using state_bounded[OF Cons(2)[unfolded split(1)] split' comp_r_qf Cons(4)]
      Cons(1)[OF init_ext split(4) Cons(4)]
    by (fastforce simp: split(1))
qed

end

fun lcp :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "lcp [] _ = 0"
| "lcp _ [] = 0"
| "lcp (a # as) (b # bs) = (if a = b then Suc (lcp as bs) else 0)"

definition lcp_dist :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat" where
  "lcp_dist as bs = length as + length bs - 2 * lcp as bs"

lemma lcp_le_min: "lcp v1 v2 \<le> min (length v1) (length v2)"
  by (induction v1 v2 rule: lcp.induct) auto

lemma lcp_zero: "lcp v1 v2 \<ge> 0"
  by auto

lemma lcp_app_le_max: "lcp (v1 @ w1) (v2 @ w2) \<le> lcp v1 v2 + max (length w1) (length w2)"
proof (induction v1 v2 rule: lcp.induct)
  case (1 v2)
  show ?case
    using lcp_le_min trans_le_add1 max.coboundedI1
    by fastforce
next
  case (2 v v1)
  show ?case
    using lcp_le_min trans_le_add2 max.coboundedI2
    by fastforce
qed auto

lemma lcp_le_sum: "lcp v1 v2 \<le> length v1 + length v2"
  using lcp_le_min trans_le_add1
  by fastforce

lemma lcp_le_app: "lcp v1 v2 \<le> lcp (v1 @ w1) (v2 @ w2)"
  by (induction v1 v2 rule: lcp.induct) auto

lemma [simp]: "lcp_dist as [] = length as" "lcp_dist [] bs = length bs"
  by (cases as) (auto simp: lcp_dist_def)

lemma lcp_dist_app_le_sum: "lcp_dist (v1 @ w1) (v2 @ w2) \<le> lcp_dist v1 v2 + length w1 + length w2"
  using lcp_le_app[of v1 v2 w1 w2]
  by (auto simp: lcp_dist_def)

lemma lcp_app_le_max_diff: "2 * lcp (v1 @ w1) (v2 @ w2) \<le>
  2 * lcp v1 v2 + length w1 + length w2 +
  max (length w1 - length w2) (length w2 - length w1)"
  using lcp_app_le_max[of v1 w1 v2 w2] lcp_app_le_max[of v2 w2 v1 w1]
  by auto

lemma lcp_dist_le_app_sum: "lcp_dist v1 v2 \<le>
  lcp_dist (v1 @ w1) (v2 @ w2) +
  max (length w1 - length w2) (length w2 - length w1)"
  using lcp_app_le_max_diff[of v1 w1 v2 w2]
  by (auto simp: lcp_dist_def)

lemma lcp_dist_same_pref: "lcp_dist (u @ v1) (u @ v2) = lcp_dist v1 v2"
  unfolding lcp_dist_def
  by (induction u) auto

(* Definition 2 *)

locale NFT =
  fixes init :: "'s"
    and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
    and accept :: "'s \<Rightarrow> bool"
    and Q :: "'s set"
  assumes finite_Q: "finite Q"
  and finite_\<delta>: "q \<in> Q \<Longrightarrow> finite {x. \<delta> q a x}"
  and init_in_Q: "init \<in> Q"
  and \<delta>_closed: "q \<in> Q \<Longrightarrow> \<delta> q a (q', bs) \<Longrightarrow> q' \<in> Q"
begin

inductive computation :: "'s \<Rightarrow> 'a list \<times> 'b list \<Rightarrow> 's \<Rightarrow> bool" ("_/\<leadsto>_/_" [64,64,64]63) where
  base[intro]: "q \<leadsto>([], []) q"
| step[intro]: "\<delta> q a (q', bs) \<Longrightarrow> q' \<leadsto>(as, bs') q'' \<Longrightarrow> q \<leadsto>(a # as, bs @ bs') q''"

definition \<tau> :: "('a list \<times> 'b list) set" where
  "\<tau> = {(as, bs). \<exists>q. init \<leadsto>(as, bs) q \<and> accept q}"

(* Definition 6 *)

definition "bv k t \<longleftrightarrow> (\<forall>f1 f2 q1 q2 a b1 b2 u v1 v2 w1 w2.
  accept f1 \<and> accept f2 \<and> q1 \<in> Q \<and> q2 \<in> Q \<and>
  init \<leadsto>(a, u @ v1) q1 \<and> q1 \<leadsto>(b1, w1) f1 \<and>
  init \<leadsto>(a, u @ v2) q2 \<and> q2 \<leadsto>(b2, w2) f2 \<and>
  length b1 + length b2 \<le> k \<longrightarrow> lcp_dist (v1 @ w1) (v2 @ w2) \<le> t)"

(* Definition 8 *)

definition active :: "'s \<Rightarrow> 'b list \<Rightarrow> bool" where
  "active q bs \<longleftrightarrow> (\<exists>q' as bs'. q \<leadsto>(as, bs @ bs') q' \<and> accept q')"

definition "bounded K \<equiv> \<forall>q q' u v v'. init \<leadsto>(u, v @ v') q \<and> active q [] \<and>
  init \<leadsto>(u, v) q' \<and> active q' v' \<longrightarrow> length v' \<le> K"

lemma no_step: "q \<leadsto>(as, bs) q' \<Longrightarrow> as = [] \<Longrightarrow> bs = [] \<and> q = q'"
  by (induction q "(as, bs)" q' rule: computation.induct) auto

lemma one_step: "\<delta> q a (q', bs) \<Longrightarrow> q \<leadsto>([a], bs) q'"
  using computation.step by fastforce

lemma step_dest: "q \<leadsto>([a], bs) q' \<Longrightarrow> \<delta> q a (q', bs)"
  apply (induction q "([a], bs)" q' rule: computation.induct)
  using computation.cases by fastforce

lemma comp_trans: "q \<leadsto>(as, bs) q' \<Longrightarrow> q' \<leadsto>(as', bs') q'' \<Longrightarrow> q \<leadsto>(as @ as', bs @ bs') q''"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma computation_snoc: "q \<leadsto>(as, bs) q' \<Longrightarrow> \<delta> q' a (q'', bs') \<Longrightarrow> q \<leadsto>(as @ [a], bs @ bs') q''"
proof -
  assume assms: "q \<leadsto>(as, bs) q'" "\<delta> q' a (q'', bs')"
  from assms(2) have "q' \<leadsto>([a], bs') q''"
    using step by fastforce
  with assms(1) show "q \<leadsto>(as @ [a], bs @ bs') q''"
    using comp_trans by auto
qed

lemma computation_split: "q \<leadsto>(as @ as', bs'') q' \<Longrightarrow>
  \<exists>q'' bs bs'. q \<leadsto>(as, bs) q'' \<and> q'' \<leadsto>(as', bs') q' \<and> bs'' = bs @ bs'"
proof (induction q "(as @ as', bs'')" q' arbitrary: as as' bs'' rule: computation.induct)
  case (step q' bs q a asa bs' q'')
  then show ?case
  proof (cases as)
    case (Cons x xs)
    then show ?thesis
      using step(1,2,4) step(3)[of xs as']
      by force
  qed auto
qed auto

lemma comp_rev_induct: "q\<leadsto>(as, bs) q' \<Longrightarrow>
  (\<And>q. P q [] [] q) \<Longrightarrow>
  (\<And>q a q' bs as bs' q''. P q as bs q'' \<Longrightarrow> q\<leadsto>(as, bs)q'' \<Longrightarrow> \<delta> q'' a (q', bs') \<Longrightarrow>
    P q (as @ [a]) (bs @ bs') q') \<Longrightarrow>
  P q as bs q'"
proof (induction as arbitrary: q bs q' rule: rev_induct)
  case Nil
  then show ?case
    using no_step
    by fastforce
next
  case (snoc x xs)
  obtain q'' cs cs' where split: "q \<leadsto>(xs, cs) q''" "q'' \<leadsto>([x], cs') q'" "bs = cs @ cs'"
    using computation_split[OF snoc(2)] by auto
  have P_xs: "P q xs cs q''"
    using snoc(1)[OF split(1) snoc(3,4)] by auto
  show ?case
    using snoc(4)[OF P_xs split(1) step_dest[OF split(2)]]
    by (auto simp add: split(3))
qed

lemma comp_closed: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> q' \<in> Q"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
     (auto simp add: \<delta>_closed)

inductive computation_ext :: "'s \<Rightarrow> 'a list \<times> ('s \<times> 'b list) list \<Rightarrow> 's \<Rightarrow> bool"
    ("_/\<leadsto>e_/_" [64,64,64]63) where
  base_ext[intro]: "q \<leadsto>e([], []) q"
| step_ext[intro]: "\<delta> q a (q', bs) \<Longrightarrow> q' \<leadsto>e(as, qs) q'' \<Longrightarrow> q \<leadsto>e(a # as, (q', bs) # qs) q''"

lemma computation_ext_no_step: "q \<leadsto>e([], []) q' \<Longrightarrow> q = q'"
  by (auto elim: computation_ext.cases)

lemma computation_ext_Cons_dest: "q\<leadsto>e(a # as', qb # qbs')q' \<Longrightarrow> \<delta> q a qb"
  by (auto elim: computation_ext.cases)

lemma computation_ext_trans: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q' \<leadsto>e(as', qs') q'' \<Longrightarrow>
  q \<leadsto>e(as @ as', qs @ qs') q''"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_length: "q \<leadsto>e(as, qs) q' \<Longrightarrow> length qs = length as"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_sound: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q \<leadsto>(as, concat (map snd qs)) q'"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct) auto

lemma computation_ext_complete: "q \<leadsto>(as, bs) q' \<Longrightarrow>
  \<exists>qs. q \<leadsto>e(as, qs) q' \<and> bs = concat (map snd qs)"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma computation_ext_split: "length as = length qbs \<Longrightarrow>
  q \<leadsto>e(as @ a # as', qbs @ (q'', bs) # qbs') q' \<Longrightarrow>
  q \<leadsto>e(as @ [a], qbs @ [(q'', bs)]) q'' \<and> q'' \<leadsto>e(as', qbs') q'"
  by (induction as qbs arbitrary: q rule: list_induct2) (auto elim: computation_ext.cases)

lemma computation_ext_closed: "q \<leadsto>e(as, qs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> (r, bs) \<in> set qs \<Longrightarrow> r \<in> Q"
  by (induction q "(as, qs)" q' arbitrary: as qs rule: computation_ext.induct)
     (auto simp add: \<delta>_closed)

definition all_trans :: "('s \<times> 'b list) set" where
  "all_trans = {x. \<exists>(q, a) \<in> (Q \<times> (UNIV :: 'a set)). \<delta> q a x}"

lemma all_trans_finite: "finite all_trans"
proof -
  have fin_Q_UNIV: "finite (Q \<times> (UNIV :: 'a set))"
    using finite_Q by auto
  have "all_trans \<subseteq> \<Union>((\<lambda>(q, a). {x. \<delta> q a x}) ` (Q \<times> (UNIV :: 'a set)))"
    unfolding all_trans_def by auto
  moreover have "finite (\<Union>((\<lambda>(q, a). {x. \<delta> q a x}) ` (Q \<times> (UNIV :: 'a set))))"
    using fin_Q_UNIV finite_\<delta> by auto
  ultimately show ?thesis
    using infinite_super by blast
qed

lemma all_trans_step: "q \<in> Q \<Longrightarrow> \<delta> q a x \<Longrightarrow> x \<in> all_trans"
  unfolding all_trans_def by auto

(* Definition 5 *)

definition output_speed :: nat where
  "output_speed = Max (length ` snd ` all_trans \<union> {1})"

lemma output_speed_step: "q \<in> Q \<Longrightarrow> \<delta> q a (q', bs) \<Longrightarrow> length bs \<le> output_speed"
  unfolding output_speed_def using all_trans_finite all_trans_step
  by (metis Max_ge UnCI finite.emptyI finite.insertI finite_UnI finite_imageI image_eqI snd_conv)

lemma output_speed_computation: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow>
  length bs \<le> length as * output_speed"
  apply (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct)
  using output_speed_step \<delta>_closed by (auto simp add: add_le_mono)

lemma output_speed_ext_computation: "q \<leadsto>e(as, qbs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> (q'', bs) \<in> set qbs \<Longrightarrow>
  length bs \<le> output_speed"
  apply (induction q "(as, qbs)" q' arbitrary: as qbs rule: computation_ext.induct)
  using output_speed_step \<delta>_closed by auto

lemma output_speed_pos: "output_speed \<ge> 1"
proof -
  have fin: "finite (length ` snd ` all_trans \<union> {1})"
    using all_trans_finite
    by auto
  show ?thesis
    using Max_ge[OF fin, of 1]
    by (auto simp add: output_speed_def)
qed

lemma computation_split_out: "q \<leadsto>(as'', bs @ bs') q' \<Longrightarrow> q \<in> Q \<Longrightarrow>
  \<exists>q'' as as' cs cs'. q \<leadsto>(as, cs) q'' \<and> q'' \<leadsto>(as', cs') q' \<and> as'' = as @ as' \<and>
    bs @ bs' = cs @ cs' \<and> length cs \<le> length bs \<and> length bs - length cs \<le> output_speed"
proof (induction q "(as'', bs @ bs')" q' arbitrary: as'' bs bs' rule: computation.induct)
  case (step q a q' bsa as bsa' q'')
  from step(1,5) have length_bsa: "length bsa \<le> output_speed"
    using output_speed_step by auto
  show ?case
  proof (cases "length bsa \<le> length bs")
    case True
    with step(4) obtain bsa'' where "bs = bsa @ bsa''"
      by (metis append_eq_append_conv_if append_eq_conv_conj)
    then show ?thesis
      using step(1,2,4,5) step(3)[of bsa'' bs'] \<delta>_closed by fastforce
  next
    case False
    with step length_bsa have "q\<leadsto>([], [])q \<and> q\<leadsto>(a # as, bsa @ bsa')q'' \<and> a # as = [] @ (a # as) \<and>
      bs @ bs' = [] @ (bsa @ bsa') \<and> length [] \<le> length bs \<and> length bs - length [] \<le> output_speed"
      using computation.step by fastforce
    then show ?thesis
      by blast
  qed
qed auto

lemma computation_ext_rem:
  assumes "q \<leadsto>e(as, qbs' @ (q', bs) # qbs'' @ (q', bs') # qbs''') q''"
  shows "\<exists>cs' cs'' cs''' c' c'' ds' bs'''.
    q \<leadsto>(cs' @ c' # cs''', ds' @ bs @ bs''') q'' \<and>
    ds' = concat (map snd qbs') \<and> bs''' = concat (map snd qbs''') \<and>
    as = cs' @ c' # cs'' @ c'' # cs''' \<and> length cs' = length qbs' \<and>
    length cs'' = length qbs'' \<and> length cs''' = length qbs'''"
proof -
  note len_as = computation_ext_length[OF assms(1), symmetric]
  obtain as' as'' as''' a a' where
    decomp': "as = as' @ [a] @ as'' @ [a'] @ as'''" "length as' = length qbs'"
    "length as'' = length qbs''" "length as''' = length qbs'''"
    using app_decomp[OF len_as]
    by (auto dest!: app_decomp[of _ "[(q', bs)]" "qbs'' @ [(q', bs')] @ qbs'''", simplified]
        app_decomp[of _ qbs'' "[(q', bs')] @ qbs'''", simplified]
        app_decomp[of _ "[(q', bs')]" "qbs'''", simplified]
        singleton_dest)
  have assoc: "q \<leadsto>e(as' @ a # as'' @ [a'] @ as''',
    qbs' @ (q', bs) # qbs'' @ [(q', bs')] @ qbs''') q''"
    using assms(1)[unfolded decomp']
    by auto
  have split: "q \<leadsto>e(as' @ [a], qbs' @ [(q', bs)]) q'" "q'\<leadsto>e(as'' @ a' # as''',
    qbs'' @ (q', bs') # qbs''') q''"
    using computation_ext_split[OF decomp'(2) assoc]
    by auto
  have split': "q' \<leadsto>e(as''', qbs''') q''"
    using computation_ext_split[OF decomp'(3) split(2)]
    by auto
  define ds' where "ds' = concat (map snd qbs')"
  define bs''' where "bs''' = concat (map snd qbs''')"
  have trans: "q \<leadsto>(as' @ [a], ds' @ bs) q'"
    using computation_ext_sound[OF split(1)]
    by (auto simp add: ds'_def)
  have trans': "q' \<leadsto>(as''', bs''') q''"
    using computation_ext_sound[OF split']
    by (auto simp add: bs'''_def)
  show ?thesis
    using comp_trans[OF trans trans'] decomp'(2,3,4)
    by (fastforce simp add: ds'_def bs'''_def decomp'(1))
qed

lemma computation_long_split: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> length as \<ge> 1 + card Q \<Longrightarrow>
  \<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' < length as"
proof -
  assume assms_comp: "q \<leadsto>(as, bs) q'" "q \<in> Q"
  obtain qbs where qbs_def: "q \<leadsto>e(as, qbs) q'" "bs = concat (map snd qbs)"
    using computation_ext_complete[OF assms_comp(1)]
    by auto
  then have qbs_len: "length qbs = length as"
    using computation_ext_length by auto
  assume assms_len: "length as \<ge> 1 + card Q"
  define qs where "qs = map fst qbs"
  have qs_sub: "set qs \<subseteq> Q"
    using computation_ext_closed[OF qbs_def(1) assms_comp(2)]
    by (auto simp add: qs_def)
  have not_distinct: "\<not>distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not>distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> 1 + card Q"
      using distinct_card[OF contr] assms_len
      by (auto simp add: qs_def qbs_len)
    show "False"
      using card_qs card_mono[OF finite_Q qs_sub]
      by auto
  qed
  obtain q'' qs' qs'' qs''' where "qs = qs' @ [q''] @ qs'' @ [q''] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  then obtain qbs' qbs'' qbs''' bs bs' where
    decomp: "qbs = qbs' @ (q'', bs) # qbs'' @ (q'', bs') # qbs'''"
    using map_ext[of fst qbs qs' "[q''] @ qs'' @ [q''] @ qs'''"]
          map_ext[of fst _ "qs''" "[q''] @ qs'''"]
    by (fastforce simp add: qs_def)
  show "\<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' < length as"
    using computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)]]
    by auto
qed

lemma comp_norm: "q \<leadsto>(as, bs) q' \<Longrightarrow> q \<in> Q \<Longrightarrow> \<exists>as' bs'. q \<leadsto>(as', bs') q' \<and> length as' \<le> card Q"
proof (induction "length as" arbitrary: as bs rule: nat_less_induct)
  case 1
  then show ?case
  proof (cases "length as \<le> card Q")
    case False
    obtain as' bs' where nex: "q \<leadsto>(as', bs') q'" "length as' < length as"
      using computation_long_split[OF 1(2,3)] False
      by auto
    then show ?thesis
      using 1(1,3)
      by auto
  qed auto
qed

lemma pumping: "q \<leadsto>(as, bs) q \<Longrightarrow> q \<leadsto>(iter_concat n as, iter_concat n bs) q"
  by (induction n) (auto intro: comp_trans)

lemma active_comp: "active q' bs \<Longrightarrow> q \<leadsto>(as, bs') q' \<Longrightarrow> active q (bs' @ bs)"
  using comp_trans
  by (fastforce simp add: active_def)

lemma active_mono: "active q (bs @ bs') \<Longrightarrow> active q bs"
  unfolding active_def by auto

lemma active_extend: "q \<leadsto>(as, bs @ bs') q' \<Longrightarrow> active q' bs \<Longrightarrow> active q bs"
  unfolding active_def using comp_trans by force

lemma active_Nil_dest: "active q [] \<Longrightarrow> q \<in> Q \<Longrightarrow>
  \<exists>as bs' q'. q \<leadsto>(as, bs') q' \<and> accept q' \<and> length as \<le> card Q \<and>
    length bs' \<le> card Q * output_speed"
  using comp_norm output_speed_computation
  apply (auto simp add: active_def)
  apply (meson dual_order.trans mult_le_mono1)
  done

(* Definition 4 *)

definition sg :: nat where
  "sg = Max ((\<lambda>q. Inf (length ` {as. \<exists>bs q'. q \<leadsto>(as, bs) q' \<and> accept q'})) `
    {q \<in> Q. active q []})"

lemma sg_le_card:
  assumes "active init []"
  shows "sg \<le> card Q"
proof -
  define Q' where "Q' = {q \<in> Q. active q []}"
  have Q'_props: "finite Q'" "Q' \<noteq> {}"
    using finite_Q assms(1) init_in_Q
    by (auto simp add: active_def Q'_def)
  have "\<And>q. q \<in> Q' \<Longrightarrow> Inf (length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}) \<le> card Q"
  proof -
    fix q
    assume in_Q': "q \<in> Q'"
    then obtain as bs q' where wit: "q\<leadsto>(as, bs)q'" "accept q'" "length as \<le> card Q"
      using active_Nil_dest
      unfolding Q'_def
      by blast
    then have len_as_in: "length as \<in> length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}"
      by auto
    show "Inf (length ` {as. \<exists>bs q'. q\<leadsto>(as, bs)q' \<and> accept q'}) \<le> card Q"
      by (rule le_trans[OF cInf_lower[OF len_as_in] wit(3)]) auto
  qed
  then show ?thesis
    using Q'_props
    by (auto simp add: sg_def Q'_def[symmetric])
qed

lemma active_Nil_dest_sg:
  assumes "active q []" "q \<in> Q"
  shows "\<exists>as bs' q'. q \<leadsto>(as, bs') q' \<and> accept q' \<and> length as \<le> sg \<and>
    length bs' \<le> sg * output_speed"
proof -
  define ass where "ass = length ` {as. \<exists>bs q'. q \<leadsto>(as, bs) q' \<and> accept q'}"
  have "ass \<noteq> {}"
    using assms(1)
    by (auto simp add: ass_def active_def)
  then have "Inf ass \<in> ass"
    using Inf_nat_def1
    by auto
  then obtain as bs q' where wit: "q \<leadsto>(as, bs) q'" "accept q'" "length as = Inf ass"
    by (auto simp add: ass_def)
  moreover have "Inf ass \<le> sg"
    using assms finite_Q
    by (auto simp add: ass_def sg_def)
  ultimately show ?thesis
    using output_speed_computation[OF wit(1) assms(2)]
    by (auto simp add: mult.commute order_subst1 intro!: exI[of _ as] exI[of _ bs] exI[of _ q'])
qed

lemma active_dest:
  assumes "active q bs" "q \<in> Q"
  shows "\<exists>as bs' q'. q \<leadsto>(as, bs @ bs') q' \<and> accept q' \<and>
    length bs' \<le> (1 + sg) * output_speed"
proof -
  obtain as bs' q' where act: "q \<leadsto>(as, bs @ bs') q'" "accept q'"
    using assms(1)
    by (auto simp add: active_def)
  then show ?thesis
  proof (cases "length bs' \<ge> output_speed")
    case True
    have app: "bs @ bs' = (bs @ take output_speed bs') @ (drop output_speed bs')"
      using True
      by auto
    obtain q'' as' as'' cs cs' where split: "q\<leadsto>(as', cs)q''" "q''\<leadsto>(as'', cs')q'"
      "as = as' @ as''"
      "(bs @ take output_speed bs') @ drop output_speed bs' = cs @ cs'"
      "length cs \<le> length (bs @ take output_speed bs')"
      "length (bs @ take output_speed bs') - length cs \<le> output_speed"
      using computation_split_out[OF act(1)[unfolded app] assms(2)]
      by auto
    obtain ds where ds_def: "cs = bs @ ds" "length ds \<le> output_speed"
      using split(5,6) True split_app[OF split(4)[unfolded app[symmetric]]]
      by fastforce
    note q''_Q = comp_closed[OF split(1) assms(2)]
    have act_q'': "active q'' []"
      using split(2) act(2)
      by (auto simp add: active_def)
    obtain es fs q''' where es_fs_def: "q''\<leadsto>(es, fs)q'''" "accept q'''" "length es \<le> sg"
      using active_Nil_dest_sg[OF act_q'' q''_Q]
      by auto
    have fs_len: "length fs \<le> sg * output_speed"
      using output_speed_computation[OF es_fs_def(1) q''_Q] es_fs_def(3)
      by (meson dual_order.trans mult_le_mono1)
    show ?thesis
      using comp_trans[OF split(1)[unfolded ds_def(1)] es_fs_def(1)] ds_def(2) fs_len es_fs_def(2)
      by fastforce
  qed fastforce
qed

lemma bounded_mono: "K \<le> K' \<Longrightarrow> bounded K \<Longrightarrow> bounded K'"
  by (fastforce simp add: bounded_def)

lemma bounded_dest: "\<And>q q' u v v'. bounded K \<Longrightarrow> init \<leadsto>(u, v @ v') q \<Longrightarrow> active q [] \<Longrightarrow>
  init \<leadsto>(u, v) q' \<Longrightarrow> active q' v' \<Longrightarrow> length v' \<le> K"
  by (auto simp add: bounded_def)

end

locale bNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> ('b :: finite) list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
fixes K :: nat
assumes bounded: "bounded K"
begin

lemmas bounded' = bounded_dest[OF bounded]

end

(* Definition 3 *)

locale kNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
fixes kv :: nat
assumes kval: "finite {bs. (as, bs) \<in> \<tau>}" "card {bs. (as, bs) \<in> \<tau>} \<le> kv"

locale fNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes functional: "(x, y) \<in> \<tau> \<Longrightarrow> (x, y') \<in> \<tau> \<Longrightarrow> y = y'"
begin

lemma one_valued: "finite {bs. (as, bs) \<in> \<tau>} \<and> card {bs. (as, bs) \<in> \<tau>} \<le> 1"
proof -
  show "finite {bs. (as, bs) \<in> \<tau>} \<and> card {bs. (as, bs) \<in> \<tau>} \<le> 1"
  proof (cases "{bs. (as, bs) \<in> \<tau>} = {}")
    case False
    then obtain bs where bs_def: "(as, bs) \<in> \<tau>"
      by auto
    have "{bs. (as, bs) \<in> \<tau>} = {bs}"
      using functional[OF bs_def]
      by (auto simp: bs_def)
    then show ?thesis
      by auto
  qed auto
qed

interpretation kNFT init \<delta> accept Q 1
  using one_valued
  by unfold_locales auto

end

locale uNFT = NFT init \<delta> accept Q
  for init :: "'s"
  and \<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and accept :: "'s \<Rightarrow> bool"
  and Q :: "'s set" +
assumes unambiguous: "init \<leadsto>e (as, qbs) f \<Longrightarrow> accept f \<Longrightarrow>
  init \<leadsto>e (as, qbs') f' \<Longrightarrow> accept f' \<Longrightarrow> qbs = qbs'"
begin

lemma functional: "(as, bs) \<in> \<tau> \<Longrightarrow> (as, bs') \<in> \<tau> \<Longrightarrow> bs = bs'"
  using unambiguous
  by (fastforce simp: \<tau>_def dest!: computation_ext_complete)

interpretation fNFT init \<delta> accept Q
  using functional
  by unfold_locales assumption

end

end