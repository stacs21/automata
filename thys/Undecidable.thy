theory Undecidable
  imports Computation
begin

datatype ('a, 's) TCell = Head 's "'a Al" | Just "'a"
datatype Move = Left | Right

instantiation Al :: (finite) finite
begin

instance
proof (standard)
  have "finite (UNIV :: 'a :: finite set)"
    using finite_UNIV by auto
  moreover have "(UNIV :: 'a :: finite Al set) \<subseteq> {Blank} \<union> Symb ` UNIV"
    apply (rule subsetI)
    subgoal for x
      by (cases x) auto
    done
  ultimately show "finite (UNIV :: 'a :: finite Al set)"
    using finite_subset by fastforce
qed

end

instantiation TCell :: (finite, finite) finite
begin

instance
proof (standard)
  have "finite (UNIV :: 'a :: finite set)" "finite ((UNIV :: 's :: finite set) \<times>
    (UNIV :: ('a :: finite) Al set))"
    using finite_UNIV by auto
  moreover have "(UNIV :: ('a :: finite, 's :: finite) TCell set) \<subseteq>
    (\<lambda>(x, y). Head x y) ` (UNIV \<times> UNIV) \<union> Just ` UNIV"
    apply (rule subsetI)
    subgoal for x
      by (cases x) auto
    done
  ultimately show "finite (UNIV :: ('a :: finite, 's :: finite) TCell set)"
    using finite_subset by fastforce
qed

end

datatype ('a, 's) Cell = Conf "('a, 's) TCell" | Sep | End_Copy | End_Sim

instantiation Cell :: (finite, finite) finite
begin

instance
proof (standard)
  have "finite (UNIV :: ('a :: finite, 's :: finite) TCell set)"
    using finite_UNIV by auto
  moreover have "(UNIV :: ('a :: finite, 's :: finite) Cell set) \<subseteq>
    Conf ` (UNIV :: ('a :: finite, 's :: finite) TCell set) \<union> {Sep, End_Copy, End_Sim}"
    apply (rule subsetI)
    subgoal for x
      by (cases x) auto
    done
  ultimately show "finite (UNIV :: ('a :: finite, 's :: finite) Cell set)"
    using finite_subset by fastforce
qed

end

datatype ('a, 's) NState = Init | Accept | Copy | PreStep "'a option" | PostStep "'s option"

instantiation NState :: (finite, finite) finite
begin

instance
proof (standard)
  have "finite (UNIV :: 'a :: finite set)" "finite (UNIV :: 's :: finite set)"
    using finite_UNIV by auto
  moreover have "(UNIV :: ('a :: finite, 's :: finite) NState set) \<subseteq>
    {Init, Accept, Copy, PreStep None} \<union>
    PreStep ` Some ` UNIV \<union> PostStep ` UNIV"
    apply (rule subsetI)
    subgoal for x
      by (cases x) auto
    done
  ultimately show "finite (UNIV :: ('a :: finite, 's :: finite) NState set)"
    using finite_subset by fastforce
qed

end

(* Definition 12 *)

locale TM =
  fixes init :: "'s :: finite"
    and step :: "'s \<Rightarrow> 'a :: finite Al \<Rightarrow> ('s \<times> 'a \<times> Move) option"
    and accept :: "'s \<Rightarrow> bool"
begin

inductive TM_step :: "('a, 's) TCell list \<Rightarrow> ('a, 's) TCell list \<Rightarrow> bool" where
  "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Left) \<Longrightarrow> TM_step (Head s ta # map Just as')
    ([Head s' Blank, Just a'] @ map Just as')"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Right) \<Longrightarrow> TM_step (map Just as @ [Head s ta])
    (map Just as @ [Just a', Head s' Blank])"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Left) \<Longrightarrow>
    TM_step (map Just as @ [Just a, Head s ta] @ map Just as')
    (map Just as @ [Head s' (Symb a), Just a'] @ map Just as')"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Right) \<Longrightarrow>
    TM_step (map Just as @ [Head s ta, Just a] @ map Just as')
    (map Just as @ [Just a', Head s' (Symb a)] @ map Just as')"

inductive reachable :: "('a, 's) TCell list \<Rightarrow> bool" where
  "reachable [Head init Blank]"
| "reachable cs \<Longrightarrow> TM_step cs cs' \<Longrightarrow> reachable cs'"

inductive nft_step :: "('a, 's) NState \<Rightarrow> ('a, 's) Cell \<Rightarrow>
  ('a, 's) NState \<times> ('a, 's) Cell list \<Rightarrow> bool" where
  "nft_step Init Sep (Copy, [Sep])"
| "nft_step Init Sep (PreStep None, [Sep, Conf (Head init Blank), Sep])"
| "nft_step Copy (Conf (Just a)) (Copy, [Conf (Just a)])"
| "nft_step Copy (Conf (Head s ta)) (Copy, [Conf (Head s ta)])"
| "nft_step Copy Sep (Copy, [Sep])"
| "nft_step (PreStep None) (Conf (Just a)) (PreStep (Some a), [])"
| "nft_step (PreStep (Some a)) (Conf (Just a')) (PreStep (Some a'), [Conf (Just a)])"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Left) \<Longrightarrow> nft_step (PreStep None) (Conf (Head s ta))
    (PostStep None, [Conf (Head s' Blank), Conf (Just a')])"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Right) \<Longrightarrow> nft_step (PreStep None) (Conf (Head s ta))
    (PostStep (Some s'), [Conf (Just a')])"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Left) \<Longrightarrow>
    nft_step (PreStep (Some a)) (Conf (Head s ta))
    (PostStep None, [Conf (Head s' (Symb a)), Conf (Just a')])"
| "\<not>accept s \<Longrightarrow> step s ta = Some (s', a', Right) \<Longrightarrow>
    nft_step (PreStep (Some a)) (Conf (Head s ta))
    (PostStep (Some s'), [Conf (Just a), Conf (Just a')])"
| "nft_step (PostStep (Some s')) (Conf (Just a)) (PostStep None, [Conf (Head s' (Symb a))])"
| "nft_step (PostStep None) (Conf (Just a)) (PostStep None, [Conf (Just a)])"
| "nft_step (PostStep (Some s')) Sep (PreStep None, [Conf (Head s' Blank), Sep])"
| "nft_step (PostStep None) Sep (PreStep None, [Sep])"
| "nft_step Copy End_Copy (Accept, [])"
| "nft_step (PreStep None) End_Sim (Accept, [])"

lemma finite_nft_step: "finite {x. nft_step q a x}"
proof -
  have "{x. nft_step q a x} \<subseteq> UNIV \<times> {xs. length xs \<le> 3}"
    by (auto elim: nft_step.cases)
  then show ?thesis
    using finite_subset finite_bounded_lists by fastforce
qed

definition "nft_accept q \<longleftrightarrow> q = Accept"

interpretation nft: NFT Init nft_step nft_accept UNIV
  apply standard
  using finite_UNIV finite_nft_step by auto

lemma PreStep_Some_Some: "nft.computation (PreStep (Some a)) (map (Conf \<circ> Just) (as @ [a']),
  (Conf (Just a)) # map (Conf \<circ> Just) as) (PreStep (Some a'))"
  using TM.nft_step.intros(7) nft.step
  by (induction as arbitrary: a) fastforce+

lemma PreStep_None_Some: "nft.computation (PreStep None) (map (Conf \<circ> Just) (as @ [a']),
  map (Conf \<circ> Just) as) (PreStep (Some a'))"
proof (cases as)
  case Nil
  show ?thesis
    using nft.one_step[OF TM.nft_step.intros(6)]
    by (auto simp add: Nil)
next
  case (Cons x xs)
  show ?thesis
    using nft.comp_trans[OF nft.one_step[OF TM.nft_step.intros(6)] PreStep_Some_Some]
    by (auto simp add: Cons)
qed

lemma PostStep_None: "nft.computation (PostStep None)
  (map (Conf \<circ> Just) as' @ [Sep], map (Conf \<circ> Just) as' @ [Sep]) (PreStep None)"
  using nft.step[OF TM.nft_step.intros(13)] nft.step[OF TM.nft_step.intros(15)]
  by (induction as') fastforce+

lemma nft_comp_Copy: "nft.computation Copy (map Conf as, map Conf as) Copy"
  using nft.step[OF TM.nft_step.intros(3)] nft.step[OF TM.nft_step.intros(4)]
  apply (induction as)
  apply auto
  by (metis TCell.exhaust)

lemma nft_comp_Copy': "nft.computation Copy (map Conf cs' @ [Sep], map Conf cs' @ [Sep]) Copy"
  using nft.comp_trans[OF nft_comp_Copy nft.one_step[OF TM.nft_step.intros(5)]] .

fun list_option :: "'a option \<Rightarrow> ('a, 's) TCell list" where
  "list_option None = []"
| "list_option (Some a) = [Just a]"

lemma TM_step_prepend: "TM_step (Just a' # ds) ds' \<Longrightarrow>
  TM_step (Just a'' # Just a' # ds) (Just a'' # ds')"
proof (induction "Just a' # ds" ds' rule: TM_step.induct)
  case (2 s ta s' a' as)
  then show ?case
    using TM_step.intros(2)[OF 2(1,2), of "a'' # as"]
    by auto
next
  case (3 s ta s' a' as a as')
  then show ?case
    using TM_step.intros(3)[OF 3(1,2), of "a'' # as" a as']
    by auto
next
  case (4 s ta s' a' as a as')
  then show ?case
    using TM_step.intros(4)[OF 4(1,2), of "a'' # as" a as']
    by auto
qed

lemma PreStep_None_PostStep: "TM_step cs cs' \<Longrightarrow> nft.computation (PreStep None)
  (map Conf cs @ [Sep], map Conf cs' @ [Sep]) (PreStep None)"
proof (induction cs cs' rule: TM_step.induct)
  case (1 s ta s' a' as')
  note step = nft.one_step[OF TM.nft_step.intros(8), OF 1]
  show ?case
    using nft.comp_trans[OF step PostStep_None]
    by auto
next
  case (2 s ta s' a' as)
  show ?case
  proof (cases as rule: rev_cases)
    case Nil
    show ?thesis
      using nft.comp_trans[OF nft.one_step[OF TM.nft_step.intros(9), OF 2]
            nft.one_step[OF TM.nft_step.intros(14)]]
      by (auto simp add: Nil)
  next
    case (snoc y ys)
    show ?thesis
      using nft.comp_trans[OF nft.comp_trans[OF PreStep_None_Some
            nft.one_step[OF TM.nft_step.intros(11), OF 2]]
            nft.one_step[OF TM.nft_step.intros(14)]]
      by (auto simp add: snoc)
    qed
next
  case (3 s ta s' a' as a as')
  show ?case
    using nft.comp_trans[OF nft.comp_trans[OF PreStep_None_Some
          nft.one_step[OF TM.nft_step.intros(10), OF 3]]
          PostStep_None]
    by auto
next
  case (4 s ta s' a' as a as')
  show ?case
  proof (cases as rule: rev_cases)
    case Nil
    show ?thesis
      using nft.comp_trans[OF nft.comp_trans[OF
            nft.one_step[OF TM.nft_step.intros(9), OF 4]
            nft.one_step[OF TM.nft_step.intros(12)]]
            PostStep_None]
      by (auto simp add: Nil)
  next
    case (snoc ys y)
    show ?thesis
      using nft.comp_trans[OF nft.comp_trans[OF nft.comp_trans[OF PreStep_None_Some
            nft.one_step[OF TM.nft_step.intros(11), OF 4]]
            nft.one_step[OF TM.nft_step.intros(12)]]
            PostStep_None]
      by (auto simp add: snoc)
  qed
qed

lemma reachable_witness: "reachable cs \<Longrightarrow> TM_step cs cs' \<Longrightarrow>
  \<exists>as bs. nft.computation Init (as, bs @ map Conf cs' @ [Sep]) (PreStep None) \<and>
  nft.computation Init (as, bs) Copy \<and>
  nft.active (PreStep None) [] \<and> nft.active Copy (map Conf cs' @ [Sep])"
proof (induction cs arbitrary: cs' rule: reachable.induct)
  case 1
  define as :: "('a, 's) Cell list" where "as = [Sep, Conf (Head init Blank), Sep]"
  define bs :: "('a, 's) Cell list" where "bs = [Sep, Conf (Head init Blank), Sep]"
  have "nft.computation Init (as, bs @ map Conf cs' @ [Sep]) (PreStep None)"
    unfolding as_def bs_def
    using nft.comp_trans[OF nft.one_step[OF TM.nft_step.intros(2)] PreStep_None_PostStep[OF 1]]
    by auto
  moreover have "nft.computation Init (as, bs) Copy"
    unfolding as_def bs_def
    using nft.comp_trans[OF nft.comp_trans[OF nft.one_step[OF TM.nft_step.intros(1)]
          nft.one_step[OF TM.nft_step.intros(4)]]
          nft.one_step[OF TM.nft_step.intros(5)]]
    by auto
  moreover have "nft.active (PreStep None) []"
    using nft.one_step[OF TM.nft_step.intros(17)]
    by (auto simp add: nft.active_def nft_accept_def)
  moreover have "nft.active Copy (map Conf cs' @ [Sep])"
    using nft.comp_trans[OF nft_comp_Copy' nft.one_step[OF TM.nft_step.intros(16)]]
    by (auto simp add: nft.active_def nft_accept_def)
  ultimately show ?case
    by auto
next
  case (2 cs cs'')
  obtain as bs where IH: "nft.computation Init (as, bs @ map Conf cs'' @ [Sep]) (PreStep None)"
    "nft.computation Init (as, bs) Copy"
    "nft.active (PreStep None) []"
    "nft.active Copy (map Conf cs'' @ [Sep])"
    using 2 by fastforce
  have "nft.active (PreStep None) []"
    using nft.one_step[OF TM.nft_step.intros(17)]
    by (auto simp add: nft.active_def nft_accept_def)
  moreover have "nft.active Copy (map Conf cs' @ [Sep])"
    using nft.comp_trans[OF nft_comp_Copy' nft.one_step[OF TM.nft_step.intros(16)]]
    by (auto simp add: nft.active_def nft_accept_def)
  ultimately show ?case
    using nft.comp_trans[OF IH(1) PreStep_None_PostStep[OF 2(4)]]
          nft.comp_trans[OF IH(2) nft_comp_Copy']
    by fastforce
qed

lemma reachable_unbounded: "reachable cs \<Longrightarrow> \<not>nft.bounded (length cs)"
proof (induction cs rule: reachable.induct)
  case 1
  have "nft.active Copy [Conf (Head init Blank), Sep]"
    using nft.comp_trans[OF nft_comp_Copy' nft.one_step[OF TM.nft_step.intros(16)],
          of "[Head init Blank]"]
    by (auto simp add: nft.active_def nft_accept_def)
  moreover have "nft.active (PreStep None) []"
    using nft.one_step[OF TM.nft_step.intros(17)]
    by (auto simp add: nft.active_def nft_accept_def)
  ultimately show ?case
    using nft.one_step[OF TM.nft_step.intros(2)] nft.one_step[OF TM.nft_step.intros(1)]
          impossible_Cons
    by (auto simp add: nft.bounded_def) fastforce
next
  case (2 cs cs')
  show ?case
    using reachable_witness[OF 2(1,2)]
    by (fastforce simp add: nft.bounded_def)
qed

lemma reachable_then_unbounded: "\<forall>n. \<exists>cs. reachable cs \<and> length cs \<ge> n \<Longrightarrow> \<not>(\<exists>K. nft.bounded K)"
  using reachable_unbounded nft.bounded_mono
  by auto

lemma nft_comp_init_unreachable: "nft.computation q (as, bs) q' \<Longrightarrow> q' = Init \<Longrightarrow>
  q = Init \<and> as = [] \<and> bs = []"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim: nft_step.cases)

lemma nft_comp_start: "nft.computation q (a # as, bs) q' \<Longrightarrow> q = Init \<Longrightarrow> a = Sep"
  by (induction q "(a # as, bs)" q' rule: nft.computation.induct) (auto elim: nft_step.cases)

lemma nft_comp_end:
  assumes "nft.computation q (as @ [Sep], bs) q'"
  shows "q' = Copy \<or> q' = PreStep None"
  apply (induction q "as @ [Sep]" "bs" q' rule: nft.comp_rev_induct)
  using assms(1) by (auto elim: nft_step.cases)

lemma nft_step_det: "nft_step s ta (s', tas) \<Longrightarrow> nft_step s ta (s'', tas') \<Longrightarrow>
  s \<noteq> Init \<Longrightarrow> s' = s'' \<and> tas = tas'"
  by (auto elim!: nft_step.cases)

lemma nft_step_init_unreachable: "nft_step s ta (s', tas) \<Longrightarrow> s' \<noteq> Init"
  by (auto elim: nft_step.cases)

lemma nft_comp_det: "nft.computation q (as, bs) q' \<Longrightarrow> nft.computation q (as, bs') q'' \<Longrightarrow>
  q \<noteq> Init \<Longrightarrow> q' = q'' \<and> bs = bs'"
proof (induction q "(as, bs)" q' arbitrary: as bs bs' q'' rule: nft.computation.induct)
  case (base q)
  then show ?case
    using nft.no_step
    by auto
next
  case (step q a q' bs as bs'' q''')
  obtain qa cs cs' where split: "nft_step q a (qa, cs)"
    "nft.computation qa (as, cs') q''" "bs' = cs @ cs'"
    using step(4) nft.computation_split[of q "[a]" as bs' q''] nft.step_dest
    by fastforce
  have step_det: "qa = q'" "bs = cs"
    using step(1,5) split(1) nft_step_det
    by auto
  have "q''' = q''" "bs'' = cs'"
    using step(3)[OF split(2)[unfolded step_det(1)]] nft_comp_init_unreachable
          nft.one_step[OF step(1)]
    by auto
  then show ?case
    using split(3) step_det
    by auto
qed

lemma PostStep_None_PreStep_None: "nft.computation q (map Conf as @ [Sep], bs') q' \<Longrightarrow>
  q = PostStep None \<Longrightarrow> q' = PreStep None \<Longrightarrow>
  \<exists>zs. as = map Just zs \<and> bs' = map (Conf \<circ> Just) zs @ [Sep]"
proof (induction q "(map Conf as @ [Sep], bs')" q' arbitrary: as bs' rule: nft.computation.induct)
  case (step q a q' bs cs bs' q'')
  show ?case
  proof (cases a)
    case Sep
    show ?thesis
      using step Sep nft.no_step
      by (cases as) (auto elim!: nft_step.cases)
  next
    case End_Copy
    show ?thesis
      using step End_Copy nft.no_step
      by (cases as) (auto elim!: nft_step.cases)
  next
    case End_Sim
    show ?thesis
      using step End_Sim nft.no_step
      by (cases as) (auto elim!: nft_step.cases)
  next
    case (Conf z)
    obtain zs where zs_def: "as = z # map Just zs" "bs' = map (Conf \<circ> Just) zs @ [Sep]"
      using step Conf
      by (cases as) (auto elim!: nft_step.cases)
    then show ?thesis
      using step Conf
      apply (cases z)
       apply (auto elim!: nft_step.cases)
      subgoal for a'
        apply (auto intro: exI[of _ "a' # zs"])
        done
      done
  qed
qed auto

lemma map_Conf: "map (\<lambda>x. Conf (Just x)) xs = map Conf ys \<Longrightarrow> map Just xs = ys"
proof -
  assume assm: "map (\<lambda>x. Conf (Just x)) xs = map Conf ys"
  then have "length xs = length ys"
    using length_map by metis
  then show "map Just xs = ys"
    using assm
    by (induction xs ys rule: list_induct2) auto
qed

lemma PreStep_run: "nft.computation q (map Conf cs @ [Sep], map Conf cs' @ [Sep]) q' \<Longrightarrow>
  q = PreStep x \<Longrightarrow> q' = PreStep None \<Longrightarrow> TM_step ((list_option x) @ cs) cs'"
proof (induction q "(map Conf cs @ [Sep], map Conf cs' @ [Sep])" q' arbitrary: cs cs' x
  rule: nft.computation.induct)
  case (step q tco q' bs as bs' q'')
  then show ?case
  proof (cases tco)
    case End_Sim
    then show ?thesis
      using step(4)
      by (cases cs) auto
  next
    case (Conf tc)
    then show ?thesis
    proof (cases tc)
      case (Head s ta)
      have noacc: "\<not>accept s"
        using step Conf Head
        by (auto elim: nft_step.cases)
      obtain ds where ds_def: "as = map Conf ds @ [Sep]" "cs = (Head s ta) # ds"
        using step(4) Conf Head
        by (cases cs) auto
      obtain s' a' dir where TM_step: "step s ta = Some (s', a', dir)"
        using step(1,6) Conf Head
        by (auto elim!: nft_step.cases)
      show ?thesis
      proof (cases "dir")
        case Left
        obtain zs where zs_def: "ds = map Just zs" "bs' = map (Conf \<circ> Just) zs @ [Sep]"
          using step Conf Head Left ds_def TM_step
          by (auto elim!: nft_step.cases dest!: PostStep_None_PreStep_None)
        show ?thesis
        proof (cases x)
          case None
          then have "cs' = [(Head s' Blank), (Just a')] @ ds"
            using step Conf Head Left TM_step
            by (auto simp add: comp_def zs_def map_Conf elim!: nft_step.cases)
          then show ?thesis
            using TM_step.intros(1)[OF noacc TM_step[unfolded Left]] None
            by (auto simp add: ds_def zs_def)
        next
          case (Some a)
          then have "cs' = [(Head s' (Symb a)), (Just a')] @ ds"
            using step Conf Head Left TM_step
            by (auto simp add: comp_def zs_def map_Conf elim!: nft_step.cases)
          then show ?thesis
            using TM_step.intros(3)[OF noacc TM_step[unfolded Left], of "[]"] Some
            by (auto simp add: ds_def zs_def)
        qed
      next
        case Right
        have q'_def: "q' = PostStep (Some s')"
          using step Conf Head Right TM_step
          by (auto elim!: nft_step.cases)
        show ?thesis
        proof (cases ds)
          case Nil
          then show ?thesis
          proof (cases x)
            case None
            then have "cs' = [Just a', Head s' Blank]"
              using step Conf Head Right Nil ds_def TM_step
              by (auto elim!: nft_step.cases dest!: nft.step_dest)
            then show ?thesis
              using TM_step.intros(2)[OF noacc TM_step[unfolded Right], of "[]"] Nil None
              by (auto simp add: ds_def)
          next
            case (Some a)
            then have "cs' = [Just a, Just a', Head s' Blank]"
              using step Conf Head Right Nil ds_def TM_step
              by (auto elim!: nft_step.cases dest!: nft.step_dest)
            then show ?thesis
              using TM_step.intros(2)[OF noacc TM_step[unfolded Right], of "[a]"] Nil Some
              by (auto simp add: ds_def)
          qed
        next
          case (Cons e es)
          obtain a'' zs where zs_def: "e = Just a''" "es = map Just zs"
            "nft.computation (PostStep None) (map Conf es @ [Sep], map (Conf \<circ> Just) zs @ [Sep])
            (PreStep None)"
            "bs' = Conf (Head s' (Symb a'')) # map (Conf \<circ> Just) zs @ [Sep]"
            apply (rule nft.computation.cases[OF step(2)])
            using q'_def ds_def Cons step(7) PostStep_None
            by (auto elim!: nft_step.cases dest!: PostStep_None_PreStep_None)
          then show ?thesis
          proof (cases x)
            case None
            then have "cs' = [Just a', (Head s' (Symb a''))] @ es"
              using step Conf Head Right Cons TM_step
              by (auto simp add: comp_def zs_def map_Conf elim!: nft_step.cases)
            then show ?thesis
              using TM_step.intros(4)[OF noacc TM_step[unfolded Right], of "[]" a'' zs] Cons None
              by (auto simp add: zs_def ds_def)
          next
            case (Some a)
            then have "cs' = [Just a, Just a', (Head s' (Symb a''))] @ es"
              using step Conf Head Right Cons TM_step
              by (auto simp add: comp_def zs_def map_Conf elim!: nft_step.cases)
            then show ?thesis
              using TM_step.intros(4)[OF noacc TM_step[unfolded Right], of "[a]" a'' zs] Cons Some
              by (auto simp add: zs_def ds_def)
          qed
        qed
      qed
    next
      case (Just a')
      obtain ds where ds_def: "as = map Conf ds @ [Sep]" "cs = Just a' # ds"
        using step(4)
        by (cases cs) (auto simp add: Conf Just)
      show ?thesis
      proof (cases x)
        case None
        then have bs'_def: "bs' = map Conf cs' @ [Sep]" "q' = PreStep (Some a')"
          using step(1,5,6)
          by (auto simp add: Conf Just elim: nft_step.cases)
        have "TM_step (Just a' # ds) cs'"
          using step(3)[unfolded ds_def bs'_def] step(7)
          by fastforce
        then show ?thesis
          using None ds_def
          by auto
      next
        case (Some a'')
        then obtain ds' where ds'_def: "bs' = map Conf ds' @ [Sep]" "cs' = Just a'' # ds'"
          "q' = PreStep (Some a')"
          using step(1,5,6)
          by (cases cs') (auto simp add: Conf Just elim!: nft_step.cases)
        have "TM_step (Just a' # ds) ds'"
          using step(3)[unfolded ds_def ds'_def] step(7)
          by fastforce
        then show ?thesis
          using TM_step_prepend
          by (auto simp add: Some ds_def ds'_def)
      qed
    qed
  qed (auto elim: nft_step.cases)
qed auto

lemma nft_comp_Copy_same:
  assumes "nft.computation q (as, bs) q'" "q' = Copy"
  shows "as = bs"
  using assms(1,2)
  apply (induction q as bs q' rule: nft.comp_rev_induct)
  using assms(1) nft_comp_init_unreachable
  by (auto elim!: nft_step.cases)+

lemma split_induct:
  "End_Copy \<notin> set cs \<Longrightarrow> End_Sim \<notin> set cs \<Longrightarrow>
  (\<And>as. P (map Conf as)) \<Longrightarrow>
  (\<And>cs as. P cs \<Longrightarrow> P (cs @ Sep # map Conf as)) \<Longrightarrow>
  P cs"
proof (induction "length cs" arbitrary: cs rule: nat_less_induct)
  case 1
  show ?case
  proof (cases "Sep \<in> set cs")
    case True
    define cs' where "cs' = rev (dropWhile (\<lambda>c. c \<noteq> Sep) (rev cs))"
    define cs'' where "cs'' = rev (takeWhile (\<lambda>c. c \<noteq> Sep) (rev cs))"
    have set_cs'': "Sep \<notin> set cs''" "End_Copy \<notin> set cs''" "End_Sim \<notin> set cs''"
      using cs''_def set_takeWhileD 1(2,3) by fastforce+
    obtain ds where ds_def: "cs' = ds @ [Sep]"
      using True cs'_def
      by (metis (mono_tags, lifting) append_Nil2 append_butlast_last_id cs''_def hd_dropWhile
          last_rev rev_is_Nil_conv set_cs''(1) set_rev takeWhile_dropWhile_id)
    have cs_split: "cs = cs' @ cs''"
      using cs'_def cs''_def
      by (metis rev_append rev_rev_ident takeWhile_dropWhile_id)
    define as where "as = map (\<lambda>c. case c of Conf c' \<Rightarrow> c') cs''"
    have "length as = length cs''"
      using as_def
      by auto
    then have cs''_Some: "cs'' = map Conf as"
      using set_cs'' as_def
      by (induction as cs'' rule: list_induct2) (auto split: Cell.splits)
    have "length ds < length cs"
      by (auto simp add: cs_split ds_def)
    then have "P ds"
      using 1 ds_def cs_split
      by (metis butlast_snoc in_set_butlast_appendI)
    then show ?thesis
      using 1 cs_split
      by (auto simp add: ds_def cs''_Some)
  next
    case False
    define as where as_def: "as = map (\<lambda>c. case c of Conf c' \<Rightarrow> c') cs"
    have "length as = length cs"
      using as_def
      by auto
    then have cs_def: "cs = map Conf as"
      using False as_def 1(2,3)
      by (induction as cs rule: list_induct2) (auto split: Cell.splits)
    show ?thesis
      using 1
      by (auto simp add: cs_def)
  qed
qed

lemma nft_step_Copy_PreStep: "nft_step Copy a (q', bs) \<Longrightarrow> q' = Copy \<or> q' = Accept"
  by (auto elim: nft_step.cases)

lemma nft_comp_Copy_PreStep: "nft.computation q (as, bs) q' \<Longrightarrow>
  q = Copy \<or> q = Accept \<Longrightarrow> q' = PreStep None \<Longrightarrow> False"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto dest: nft_step_Copy_PreStep elim: nft_step.cases)

lemma nft_step_PreStep_Copy: "nft_step q a (Copy, bs) \<Longrightarrow>
  q = Init \<or> q = Copy"
  by (auto elim: nft_step.cases)

lemma nft_comp_PreStep_Copy:
  assumes "nft.computation q (as, bs) q'" "q = PreStep None" "q' = Copy"
  shows "False"
  using assms(1,2,3)
  apply (induction q as bs q' rule: nft.comp_rev_induct)
  using assms(1) nft_comp_init_unreachable
  by (auto dest!: nft_step_PreStep_Copy)+

lemma nft_step_Some: "nft_step q (Conf a) (q', bs) \<Longrightarrow>
  Sep \<notin> set bs \<and> End_Sim \<notin> set bs \<and> End_Copy \<notin> set bs"
  by (auto elim: nft_step.cases)

lemma nft_step_None: "nft_step q Sep (q', bs) \<Longrightarrow> q \<noteq> Init \<Longrightarrow> \<exists>as. bs = map Conf as @ [Sep]"
  apply (auto elim!: nft_step.cases)
  by (metis Nil_is_map_conv list.simps(9))

lemma nft_comp_Some: "nft.computation q (map Conf as, bs) q' \<Longrightarrow>
  Sep \<notin> set bs \<and> End_Sim \<notin> set bs \<and> End_Copy \<notin> set bs"
  by (induction q "(map Conf as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto dest: nft_step_Some)

lemma nft_comp_PreStep_None:
  assumes "nft.computation (PreStep None) (map Conf as @ [Sep], bs) q'"
  shows "\<exists>as'. bs = map Conf as' @ [Sep]"
proof -
  obtain cs cs' q'' where split: "nft.computation (PreStep None) (map Conf as, cs) q''"
    "nft_step q'' Sep (q', cs')" "bs = cs @ cs'"
    using nft.computation_split[OF assms] by (auto dest: nft.step_dest)
  obtain ds where ds_def: "cs = map Conf ds"
    using nft_comp_Some[OF split(1)]
    by (metis (full_types) ex_map_conv Cell.exhaust)
  have "q'' \<noteq> Init"
    using nft_comp_init_unreachable[OF split(1)]
    by auto
  then obtain es where es_def: "cs' = map Conf es @ [Sep]"
    using nft_step_None[OF split(2)]
    by auto
  show ?thesis
    using split(3) ds_def es_def
    by (metis append_assoc map_append)
qed

lemma nft_comp_PreStep_None_length:
  assumes "nft.computation (PreStep None) (map Conf as @ [Sep], bs) (PreStep None)"
  shows "length bs \<ge> length as + 1"
proof -
  obtain as' where bs_def: "bs = map Conf as' @ [Sep]"
    using nft_comp_PreStep_None[OF assms]
    by auto
  have "TM_step as as'"
    using PreStep_run[OF assms[unfolded bs_def]]
    by auto
  then show ?thesis
    unfolding bs_def
    by (auto elim: TM_step.cases)
qed

lemma nft_comp_PreStep_None_length':
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
    "nft.computation (PreStep None) (cs @ [Sep], bs) (PreStep None)"
  shows "length bs \<ge> length cs + 1"
  using assms(3)
proof (induction cs arbitrary: bs rule: split_induct)
  case (3 as)
  then show ?case
    using nft_comp_PreStep_None_length
    by auto
next
  case (4 cs as)
  obtain qm ds ds' where split: "nft.computation (PreStep None) (cs @ [Sep], ds) qm"
    "nft.computation qm (map Conf as @ [Sep], ds') (PreStep None)" "bs = ds @ ds'"
    using nft.computation_split[of _ "cs @ [Sep]"] 4(2)
    by fastforce
  have qm_def: "qm = PreStep None"
    using nft_comp_end[OF split(1)] nft_comp_Copy_PreStep[OF split(2)]
    by auto
  show ?case
    using 4(1)[OF split(1)[unfolded qm_def]]
          nft_comp_PreStep_None_length[OF split(2)[unfolded qm_def]]
    by (auto simp add: split(3))
qed (auto simp add: assms(1,2))

lemma nft_comp_Init_PreStep_length:
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
    "nft.computation Init (cs @ [Sep], bs) q" "q = PreStep None"
  shows "length bs \<ge> length cs + 2"
  using assms
proof (cases cs)
  case (Cons a as)
  have a_None: "a = Sep"
    using assms nft_comp_start
    by (auto simp add: Cons)
  have comp: "nft.computation Init (a # as @ [Sep], bs) (PreStep None)"
    using assms
    by (auto simp add: Cons)
  obtain ds where split: "nft.computation (PreStep None) (as @ [Sep], ds) (PreStep None)"
    "bs = [Sep, Conf (Head init Blank), Sep] @ ds"
    apply (rule nft.computation.cases[OF comp])
    using nft_comp_Copy_PreStep
    by (fastforce elim!: nft_step.cases)+
  show ?thesis
    using nft_comp_PreStep_None_length'[OF _ _ split(1)] split(2) assms
    by (auto simp add: Cons)
qed (auto dest!: nft.step_dest elim: nft_step.cases)[1]

lemma split_app: "xs @ [Sep] @ map Conf as = ys @ map Conf bs \<Longrightarrow>
  \<exists>zs. ys = xs @ [Sep] @ zs"
proof (induction as arbitrary: bs rule: rev_induct)
  case (snoc z zs)
  then show ?case
    by (cases bs rule: rev_cases) auto
qed (metis last_appendR last_map last_snoc list.map_disc_iff Cell.simps(3) self_append_conv)

lemma split_app_length: "xs @ [Sep] @ ws = ys @ map Conf bs \<Longrightarrow> \<exists>zs. ys = xs @ [Sep] @ zs"
proof (induction bs arbitrary: xs ys ws rule: rev_induct)
  case (snoc z zs)
  then show ?case
    by (cases ws rule: rev_cases) auto
qed auto

lemma split_app':
  assumes "xs @ [Sep] @ map Conf as @ [Sep] @ rs = ys @ map Conf bs @ [Sep]"
  shows "\<exists>zs. ys = xs @ [Sep] @ zs"
  using assms
proof (cases rs rule: rev_cases)
  case Nil
  then show ?thesis
    using assms split_app
    by fastforce
next
  case (snoc ws w)
  have cut_last: "(xs @ [Sep] @ map Conf as) @ [Sep] @ ws = ys @ map Conf bs"
    using assms
    by (auto simp add: snoc)
  then show ?thesis
    using split_app_length[OF cut_last]
    by fastforce
qed

lemma split_None: "map Conf xs @ [Sep] @ xs' = map Conf ys @ [Sep] @ ys' \<Longrightarrow> xs = ys"
proof (induction xs arbitrary: xs' ys ys')
  case (Cons z zs)
  then show ?case
    by (cases ys) auto
qed (metis Cell.distinct(1) hd_append list.map_sel(1) list.sel(1) map_is_Nil_conv not_Cons_self2)

lemma nft_comp_reach:
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
  "nft.computation Init (Sep # cs @ Sep # map Conf as @ [Sep], bs) Copy"
  "nft.computation Init (Sep # cs @ Sep # map Conf as @ [Sep], bs @ bs') (PreStep None)"
  shows "\<exists>as'. reachable as \<and> TM_step as as' \<and> bs' = map Conf as' @ [Sep]"
  using assms
proof (induction cs arbitrary: as bs bs' rule: split_induct)
  case (3 as')
  have bs_def: "bs = Sep # map Conf as' @ Sep # map Conf as @ [Sep]"
    using nft_comp_Copy_same[OF 3(3)]
    by auto
  obtain qi cs cs' where split: "nft_step Init Sep (qi, cs)"
    "nft.computation qi (map Conf as' @ Sep # map Conf as @ [Sep], cs') (PreStep None)"
    "bs @ bs' = cs @ cs'"
    using 3(4) nft.computation.cases
    by blast
  have qi_props: "qi = PreStep None" "cs = Sep # map Conf [Head init Blank] @ [Sep]"
    using split(1,2) nft_comp_Copy_PreStep
    by (fastforce elim!: nft_step.cases)+
  have as'_def: "as' = [Head init Blank]"
    using split(3)[unfolded bs_def qi_props(2)] split_None[of as' "map Conf as @ [Sep] @ bs'"]
    by auto
  obtain qm ds ds' where qm_def: "nft.computation (PreStep None) (map Conf as' @ [Sep], ds) qm"
    "nft.computation qm (map Conf as @ [Sep], ds') (PreStep None)" "cs' = ds @ ds'"
    using nft.computation_split[of qi "map Conf as' @ [Sep]" "map Conf as @ [Sep]"]
          split(2) qi_props(1)
    by fastforce
  have qm_props: "qm = PreStep None"
    using nft_comp_end[OF qm_def(1)] nft_comp_PreStep_Copy[OF qm_def(1)]
    by auto
  obtain dsa dsa' where dsa_def: "ds = map Conf dsa @ [Sep]" "ds' = map Conf dsa' @ [Sep]"
    using nft_comp_PreStep_None[OF qm_def(1)] nft_comp_PreStep_None[OF qm_def(2)[unfolded qm_props]]
    by auto
  have tm_step: "TM_step as' dsa" "TM_step as dsa'"
    using PreStep_run[OF qm_def(1)[unfolded dsa_def] _ qm_props]
          PreStep_run[OF qm_def(2)[unfolded qm_props dsa_def]]
    by auto
  have as_dsa: "as = dsa" "bs' = map Conf dsa' @ [Sep]"
    using split(3)[unfolded bs_def qi_props qm_def(3) dsa_def] as'_def split_None
    by auto
  then show ?case
    using tm_step(1)[unfolded as'_def as_dsa[symmetric]] tm_step(2)
    by (auto intro: reachable.intros)
next
  case (4 cs as')
  have bs_comp: "nft.computation Init ((Sep # cs @ Sep # map Conf as' @ [Sep]) @
    map Conf as @ [Sep], bs) Copy"
    using 4(4) by auto
  then obtain ds ds' qd where bs_split:
    "nft.computation Init (Sep # cs @ Sep # map Conf as' @ [Sep], ds) qd"
    "nft.computation qd (map Conf as @ [Sep], ds') Copy"
    "bs = ds @ ds'"
    using nft.computation_split by blast
  have qd_def: "qd = Copy"
  proof -
    have "qd = Copy \<or> qd = PreStep None"
      using nft_comp_end[of _ "Sep # cs @ Sep # map Conf as'"] bs_split(1)
      by auto
    then show ?thesis
      using nft_comp_PreStep_Copy[OF bs_split(2)]
      by auto
  qed
  have bs_def: "bs = (Sep # cs @ Sep # map Conf as' @ [Sep]) @ map Conf as @ [Sep]"
    using nft_comp_Copy_same[OF bs_comp]
    by auto
  have ds_def: "ds = Sep # cs @ Sep # map Conf as' @ [Sep]"
    using nft_comp_Copy_same[OF bs_split(1) qd_def]
    by auto
  have ds'_def: "ds' = map Conf as @ [Sep]"
    using nft_comp_Copy_same[OF bs_split(2)]
    by auto
  have bs_bs'_comp: "nft.computation Init ((Sep # cs @ Sep # map Conf as' @ [Sep]) @
    map Conf as @ [Sep], bs @ bs') (PreStep None)"
    using 4(5) by auto
  then obtain es es' qe where bs'_split:
    "nft.computation Init (Sep # cs @ Sep # map Conf as' @ [Sep], es) qe"
    "nft.computation qe (map Conf as @ [Sep], es') (PreStep None)"
    "bs @ bs' = es @ es'"
    using nft.computation_split by blast
  have qe_def: "qe = PreStep None"
  proof -
    have "qe = Copy \<or> qe = PreStep None"
      using nft_comp_end[of _ "Sep # cs @ Sep # map Conf as'"] bs'_split(1)
      by auto
    then show ?thesis
      using nft_comp_Copy_PreStep[OF bs'_split(2)]
      by auto
  qed
  obtain fs where fs_def: "es' = map Conf fs @ [Sep]"
    using nft_comp_PreStep_None[OF bs'_split(2)[unfolded qe_def]]
    by auto
  obtain zs where zs_def: "es = ds @ zs"
    using split_app'[of "Sep # cs @ Sep # map Conf as'" as bs' es fs] ds_def
          bs'_split(3)[unfolded bs_def fs_def]
    by auto
  obtain ns where ns_def: "reachable as'" "TM_step as' ns" "zs = map Conf ns @ [Sep]"
    using 4(1)[OF _ _ bs_split(1)[unfolded qd_def] bs'_split(1)[unfolded qe_def zs_def]] 4(2,3)
    by auto
  have as_ns: "ns = as" "bs' = map Conf fs @ [Sep]"
    using bs'_split(3)[unfolded zs_def ns_def(3) fs_def bs_def ds_def] split_None
    by auto
  have "nft.computation (PreStep None) (map Conf as @ [Sep], map Conf fs @ [Sep]) (PreStep None)"
    using bs'_split(2)[unfolded qe_def] fs_def
    by auto
  then have "TM_step as fs"
    using PreStep_run
    by fastforce
  then show ?case
    using ns_def(1,2)[unfolded as_ns(1)] as_ns(2)
    by (auto intro: reachable.intros(2))
qed (auto simp add: assms(1,2))

lemma init_reaches_states:
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
    "nft.computation Init (Sep # cs @ [Sep], bs) q"
    "nft.computation Init (Sep # cs @ [Sep], bs @ bs') q'"
    "bs' \<noteq> []"
  shows "q = Copy \<and> q' = PreStep None"
proof -
  have comps: "nft.computation Init ((Sep # cs) @ [Sep], bs) q"
    "nft.computation Init ((Sep # cs) @ [Sep], bs @ bs') q'"
    using assms(3,4)
    by auto
  have q_neq_q': "q \<noteq> q'"
  proof - 
    obtain qm ds ds' where qm_def: "qm = Copy \<or> qm = PreStep None"
      "nft_step Init Sep (qm, ds)"
      "nft.computation qm (cs @ [Sep], ds') q"
      "bs = ds @ ds'"
      by (rule nft.computation.cases[OF comps(1)])
         (auto elim!: nft_step.cases intro: nft_step.intros)
    have qm_q: "qm = q"
      using qm_def(1) nft_comp_end[OF qm_def(3)]
            nft_comp_PreStep_Copy[OF qm_def(3)] nft_comp_Copy_PreStep[OF qm_def(3)]
      by auto
    obtain qm' es es' where qm'_def: "qm' = Copy \<or> qm' = PreStep None"
      "nft_step Init Sep (qm', es)"
      "nft.computation qm' (cs @ [Sep], es') q'"
      "bs @ bs' = es @ es'"
      by (rule nft.computation.cases[OF comps(2)])
         (auto elim!: nft_step.cases intro: nft_step.intros)
    have qm'_q': "qm' = q'"
      using qm'_def(1) nft_comp_end[OF qm'_def(3)]
            nft_comp_PreStep_Copy[OF qm'_def(3)] nft_comp_Copy_PreStep[OF qm'_def(3)]
      by auto
    show ?thesis
      using qm_def qm'_def nft_comp_det[OF qm_def(3), of es' q'] assms(5)
      unfolding qm_q qm'_q'
      by (auto elim!: nft_step.cases)
  qed
  show "q = Copy \<and> q' = PreStep None"
    using nft_comp_end[OF comps(1)] nft_comp_end[OF comps(2)] q_neq_q'
          nft_comp_Init_PreStep_length[OF _ _ comps(1)]
          nft_comp_Init_PreStep_length[OF _ _comps(2)]
          nft_comp_Copy_same[OF comps(1)]
          nft_comp_Copy_same[OF comps(2)] assms(1,2)
    by auto (metis le_add1 length_Cons length_append length_append_singleton not_less_eq_eq)+
qed

lemma init_reach:
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
    "nft.computation Init (cs @ [Sep], bs) q"
    "nft.computation Init (cs @ [Sep], bs @ bs') q'" "bs' \<noteq> []"
  shows "\<exists>as. reachable as \<and> length as \<ge> length bs' - 1"
  using assms
proof (induction cs rule: split_induct)
  case (3 as)
  have as_Nil: "as = []"
    using nft_comp_start 3(3)
    by (cases as) fastforce+
  have step: "bs' = [Conf (Head init Blank), Sep]"
    using nft_comp_end[OF 3(3)] nft_comp_end[OF 3(4)]
          nft_comp_Copy_same[OF 3(3)] 3(3,4,5)
    by (auto simp add: as_Nil dest!: nft.step_dest elim!: nft_step.cases)
  then show ?case
    by (auto intro: reachable.intros)
next
  case (4 cs as)
  show ?case
  proof (cases cs)
    case Nil
    have sts: "q = Copy" "q' = PreStep None"
      using init_reaches_states[of "map Conf as" bs q bs' q'] 4(4,5,6)
      by (auto simp add: Nil)
    have bs_def: "bs = Sep # map Conf as @ [Sep]"
      using nft_comp_Copy_same[OF 4(4)[unfolded sts]]
      by (auto simp add: Nil)
    have comp: "nft.computation Init (Sep # map Conf as @ [Sep], bs @ bs') (PreStep None)"
      using 4(5)
      by (auto simp add: Nil sts)
    obtain ds where ds_def:
      "nft.computation (PreStep None) (map Conf as @ [Sep], ds) (PreStep None)"
      "bs @ bs' = [Sep] @ map Conf [Head init Blank] @ [Sep] @ ds"
      apply (rule nft.computation.cases[OF comp])
      using nft_comp_Copy_PreStep by (fastforce elim!: nft_step.cases)+
    have as_def: "as = [Head init Blank]"
      using ds_def(2) split_None[of as]
      by (auto simp add: bs_def)
    obtain es where es_def: "ds = map Conf es @ [Sep]"
      using nft_comp_PreStep_None[OF ds_def(1)]
      by auto
    have tm_step: "TM_step as es"
      using PreStep_run[OF ds_def(1)[unfolded es_def]]
      by auto
    have bs'_def: "bs' = ds"
      using ds_def(2)[unfolded bs_def] as_def
      by auto
    show ?thesis
      using tm_step
      by (auto simp add: as_def bs'_def es_def intro: reachable.intros)
  next
    case (Cons c cs')
    have c_None: "c = Sep"
      using 4(4)[unfolded Cons] nft_comp_start
      by auto
    show ?thesis
      using nft_comp_reach[of cs' as bs bs'] 4
            init_reaches_states[of "cs' @ Sep # map Conf as"]
      apply (auto simp add: Cons c_None intro: reachable.intros)
      by (metis (no_types, lifting) One_nat_def diff_Suc_1 le_refl length_append_singleton
          length_map reachable.intros(2))
  qed
qed (auto simp add: assms(1,2))

lemma PostStep_run_len:
  assumes "nft.computation (PostStep x) (map Conf as, ds') q"
  shows "length ds' = length as"
  using assms
proof (induction as arbitrary: x ds' q)
  case Nil
  then show ?case
    by (auto dest: nft.no_step)
next
  case (Cons a as)
  have comp: "nft.computation (PostStep x) (Conf a # map Conf as, ds') q"
    using Cons(2)
    by auto
  obtain e es' where rest: "nft.computation (PostStep None) (map Conf as, es') q" "ds' = e # es'"
    by (rule nft.computation.cases[OF comp]) (auto elim: nft_step.cases)
  show ?case
    using Cons(1)[OF rest(1)]
    by (auto simp add: rest(2) split: option.splits)
qed

lemma PreStep_run_len:
  assumes "nft.computation (PreStep x) (map Conf as, ds') q"
  shows "length ds' \<le> length as + 1 \<and>
    length as \<le> length ds' + 2 - (case x of None \<Rightarrow> 0 | _ \<Rightarrow> 1)"
  using assms
proof (induction as arbitrary: x ds' q)
  case Nil
  then show ?case
    by (auto dest: nft.no_step)
next
  case (Cons a as)
  show ?case
  proof (cases a)
    case (Head s ta)
    have comp: "nft.computation (PreStep x) (Conf a # map Conf as, ds') q"
      using Cons(2)
      by auto
    obtain x' es es' where rest: "nft.computation (PostStep x') (map Conf as, es') q"
      "ds' = es @ es'" "length es \<le> 2"
      apply (rule nft.computation.cases[OF comp])
      using Head by (auto elim: nft_step.cases)
    show ?thesis
      using PostStep_run_len[OF rest(1)] rest(3)
      by (auto simp add: rest(2) split: option.splits)
  next
    case (Just a')
    have comp: "nft.computation (PreStep x) (Conf (Just a') # map Conf as, ds') q"
      using Cons(2)
      by (auto simp add: Just)
    obtain es where es_def: "nft.computation (PreStep (Some a')) (map Conf as, es) q"
      "length ds' = (case x of None \<Rightarrow> 0 | _ \<Rightarrow> 1) + length es"
      by (rule nft.computation.cases[OF comp]) (auto elim: nft_step.cases)
    show ?thesis
      using Cons(1)[OF es_def(1)]
      by (auto simp add: es_def(2) split: option.splits)
  qed
qed

lemma nft_comp_Accept: "nft.computation q (as, bs) q' \<Longrightarrow>
  q = Accept \<Longrightarrow> as = [] \<and> bs = [] \<and> q' = Accept"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim: nft_step.cases)

lemma nft_comp_Accept': "nft.computation q (as, bs) q' \<Longrightarrow>
  q \<noteq> Accept \<Longrightarrow> q' = Accept \<Longrightarrow> End_Sim \<in> set as \<or> End_Copy \<in> set as"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim: nft_step.cases)

lemma nft_comp_Copy_Copy: "nft.computation q (as, bs) q' \<Longrightarrow> q = Copy \<Longrightarrow>
  q' = Copy \<or> q' = Accept"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim: nft_step.cases dest: nft_comp_Accept)

lemma nft_comp_Copy_Copy':
  assumes "nft.computation q (as, bs) q'" "q' = Copy"
  shows "q = Copy \<or> q = Init"
  using assms
  apply (induction q as bs q' rule: nft.comp_rev_induct)
  using nft_comp_init_unreachable assms(1)
  by (auto elim: nft_step.cases)

lemma split_app_long:
  assumes "length ds + n \<le> length es" "ds @ ds' = es @ es'"
  shows "\<exists>rs. es = ds @ rs \<and> length rs \<ge> n"
  using assms
  apply (induction ds arbitrary: n ds' es es')
   apply auto
  by (metis Nat.le_diff_conv2 add.commute add_Suc_right add_leD1 append_Cons
      append_eq_append_conv_if append_eq_conv_conj length_Cons length_drop)

lemma init_reach':
  assumes "End_Copy \<notin> set cs" "End_Sim \<notin> set cs"
    "nft.computation Init (cs, bs) q"
    "nft.computation Init (cs, bs @ bs') q'" "bs' \<noteq> []" "length bs' \<ge> 4"
  shows "\<exists>as. reachable as \<and> length as \<ge> length bs' - 4"
  using assms
proof (induction cs rule: split_induct)
  case (3 as)
  show ?case
    using 3
    by (cases as) (auto dest: nft_comp_start nft.no_step)
next
  case (4 cs as)
  obtain qm ds ds' where split: "nft.computation Init (cs @ [Sep], ds) qm"
    "nft.computation qm (map Conf as, ds') q" "bs = ds @ ds'"
    using nft.computation_split[of _ "cs @ [Sep]"] 4(4)
    by fastforce
  have qm_def: "qm = Copy \<or> qm = PreStep None"
    using nft_comp_end[OF split(1)] .
  then have len_ds': "length ds' \<le> length as + 1 \<and> length as \<le> length ds' + 2"
  proof (rule disjE)
    assume lassm: "qm = Copy"
    then show "length ds' \<le> length as + 1 \<and> length as \<le> length ds' + 2"
      using nft_comp_Copy_same[OF split(2)] nft_comp_Copy_Copy[OF split(2)]
            nft_comp_Accept'[OF split(2)] 4(2,3)
      by fastforce
  next
    assume lassm: "qm = PreStep None"
    show "length ds' \<le> length as + 1 \<and> length as \<le> length ds' + 2"
      using PreStep_run_len[OF split(2)[unfolded lassm]]
      by auto
  qed
  obtain qm' es es' where split': "nft.computation Init (cs @ [Sep], es) qm'"
    "nft.computation qm' (map Conf as, es') q'" "bs @ bs' = es @ es'"
    using nft.computation_split[of Init "cs @ [Sep]" "map Conf as" "bs @ bs'" q'] 4(5)
    by fastforce
  have qm'_def: "qm' = Copy \<or> qm' = PreStep None"
    using nft_comp_end[OF split'(1)] .
  then have len_es': "length es' \<le> length as + 1 \<and> length as \<le> length es' + 2"
  proof (rule disjE)
    assume lassm: "qm' = Copy"
    then show "length es' \<le> length as + 1 \<and> length as \<le> length es' + 2"
      using nft_comp_Copy_same[OF split'(2)] nft_comp_Copy_Copy[OF split'(2)]
            nft_comp_Accept'[OF split'(2)] 4(2,3)
      by fastforce
  next
    assume lassm: "qm' = PreStep None"
    show "length es' \<le> length as + 1 \<and> length as \<le> length es' + 2"
      using PreStep_run_len[OF split'(2)[unfolded lassm]]
      by auto
  qed
  have "length es \<ge> length ds + (length bs' - 3)"
  proof -
    have len_es'_le: "length es' \<le> length ds' + 3"
      using len_es' len_ds'
      by auto
    have "length es = length ds + length ds' + length bs' - length es'"
      using split'(3)[unfolded split(3)]
      by (metis add_diff_cancel_right' length_append)
    then show ?thesis
      using len_es'_le 4(7)
      by auto
  qed
  then obtain rs where rs_def: "es = ds @ rs" "length rs \<ge> length bs' - 3"
    using split'(3)[unfolded split(3)] split_app_long[of _ _ es "ds' @ bs'" es']
    by auto
  moreover have "rs \<noteq> []"
    using rs_def(2) 4(7)
    by auto
  ultimately show ?case
    using init_reach[OF _ _ split(1) split'(1)[unfolded rs_def]] 4(2,3)
    by auto
qed (auto simp add: assms(1,2))

lemma nft_comp_End_Copy: "nft.computation q (as, bs) q' \<Longrightarrow> End_Copy \<in> set as \<Longrightarrow>
  \<exists>cs. as = cs @ [End_Copy] \<and> End_Copy \<notin> set cs \<and> End_Sim \<notin> set cs"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim!: nft_step.cases dest: nft_comp_Accept)

lemma nft_comp_End_Sim: "nft.computation q (as, bs) q' \<Longrightarrow> End_Sim \<in> set as \<Longrightarrow>
  \<exists>cs. as = cs @ [End_Sim] \<and> End_Copy \<notin> set cs \<and> End_Sim \<notin> set cs"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: nft.computation.induct)
     (auto elim!: nft_step.cases dest: nft_comp_Accept)

lemma unbounded_then_reachable: "\<forall>K. \<not>nft.bounded K \<Longrightarrow> \<forall>n. \<exists>cs. reachable cs \<and> length cs \<ge> n"
proof (rule allI)
  fix n
  assume assm: "\<forall>K. \<not>nft.bounded K"
  then obtain q q' u v v' where wit: "nft.computation Init (u, v) q'"
    "nft.computation Init (u, v @ v') q" "length v' \<ge> n + 4"
    using nft.bounded_def[of "n + 4"]
    by fastforce
  show "\<exists>cs. reachable cs \<and> length cs \<ge> n"
  proof (cases "End_Copy \<notin> set u \<and> End_Sim \<notin> set u")
    case True
    then show ?thesis
      using init_reach'[OF _ _ wit(1,2)] wit(3)
      by fastforce
  next
    case False
    then have "End_Copy \<in> set u \<or> End_Sim \<in> set u"
      by auto
    then show ?thesis
    proof (rule disjE)
      assume "End_Copy \<in> set u"
      then obtain ds where ds_def: "u = ds @ [End_Copy]" "End_Copy \<notin> set ds" "End_Sim \<notin> set ds"
        using nft_comp_End_Copy[OF wit(1)]
        by auto
      obtain q'' es es' where split: "nft.computation Init (ds, es) q''"
        "nft_step q'' End_Copy (q', es')" "v = es @ es'"
        using nft.computation_split[OF wit(1)[unfolded ds_def(1)]]
        by (auto dest: nft.step_dest)
      have es_v: "es = v"
        using split(2,3)
        by (auto elim: nft_step.cases)
      obtain q''' fs fs' where split': "nft.computation Init (ds, fs) q'''"
        "nft_step q''' End_Copy (q, fs')" "v @ v' = fs @ fs'"
        using nft.computation_split[OF wit(2)[unfolded ds_def(1)]]
        by (auto dest: nft.step_dest)
      have fs_v: "fs = v @ v'"
        using split'(2,3)
        by (auto elim: nft_step.cases)
      show "\<exists>cs. reachable cs \<and> n \<le> length cs"
        using init_reach'[OF _ _ split(1)[unfolded es_v] split'(1)[unfolded fs_v]] ds_def(2,3)
              wit(3)
        by fastforce
    next
      assume "End_Sim \<in> set u"
      then obtain ds where ds_def: "u = ds @ [End_Sim]" "End_Copy \<notin> set ds" "End_Sim \<notin> set ds"
        using nft_comp_End_Sim[OF wit(1)]
        by auto
      obtain q'' es es' where split: "nft.computation Init (ds, es) q''"
        "nft_step q'' End_Sim (q', es')" "v = es @ es'"
        using nft.computation_split[OF wit(1)[unfolded ds_def(1)]]
        by (auto dest: nft.step_dest)
      have es_v: "es = v"
        using split(2,3)
        by (auto elim: nft_step.cases)
      obtain q''' fs fs' where split': "nft.computation Init (ds, fs) q'''"
        "nft_step q''' End_Sim (q, fs')" "v @ v' = fs @ fs'"
        using nft.computation_split[OF wit(2)[unfolded ds_def(1)]]
        by (auto dest: nft.step_dest)
      have fs_v: "fs = v @ v'"
        using split'(2,3)
        by (auto elim: nft_step.cases)
      show "\<exists>cs. reachable cs \<and> n \<le> length cs"
        using init_reach'[OF _ _ split(1)[unfolded es_v] split'(1)[unfolded fs_v]] ds_def(2,3)
              wit(3)
        by fastforce
    qed
  qed
qed

lemma unambiguous_aux: "nft.computation_ext q (as, qbs) f \<Longrightarrow>
  nft.computation_ext q (as, qbs') f' \<Longrightarrow> q \<noteq> Init \<Longrightarrow> qbs = qbs'"
proof (induction q "(as, qbs)" f arbitrary: as qbs qbs' rule: nft.computation_ext.induct)
  case (step_ext q a q' bs as qs q'')
  then show ?case
  proof (cases qbs')
    case (Cons qb qbs'')
    have q'_not_Init: "q' \<noteq> Init"
      using step_ext(1)
      by (auto elim: nft_step.cases)
    have "nft_step q a qb"
      using step_ext(4)
      by (auto simp: Cons elim: nft.computation_ext.cases)
    then have qb_def: "qb = (q', bs)"
      using step_ext(1,5)
      by (auto elim!: nft_step.cases)
    have comp': "nft.computation_ext q' (as, qbs'') f'"
      using step_ext(4)
      by (auto simp: Cons qb_def elim: nft.computation_ext.cases)
    show ?thesis
      using step_ext(3)[OF comp' q'_not_Init]
      by (auto simp: Cons qb_def)
  qed (auto elim: nft.computation_ext.cases)
qed (auto elim: nft.computation_ext.cases)

lemma unambiguous:
  assumes "nft.computation_ext Init (as, qbs) f" "nft_accept f"
    "nft.computation_ext Init (as, qbs') f'" "nft_accept f'"
  shows "qbs = qbs'"
proof (rule nft.computation_ext.cases[OF assms(1)])
  assume "(as, qbs) = ([], [])"
  then show "qbs = qbs'"
    using assms(3)
    by (auto elim: nft.computation_ext.cases)
next
  fix q a q' bs as' qbs'' q''
  assume lassms: "Init = q" "(as, qbs) = (a # as', (q', bs) # qbs'')"
    "f = q''" "nft_step q a (q', bs)" "nft.computation_ext q' (as', qbs'') q''"
  note fst_step = lassms(4)[folded lassms(1)]
  note comp = nft.computation_ext_sound[OF lassms(5)]
  have q'_mode: "q' = Copy \<or> q' = PreStep None"
    using fst_step
    by (auto elim: nft_step.cases)
  then have q'_not_Init_Accept: "q' \<noteq> Init" "q' \<noteq> Accept"
    by auto
  have a_def: "a = Sep"
    using fst_step
    by (auto elim: nft_step.cases)
  have q''_def: "q'' = Accept"
    using assms(2)
    by (auto simp: lassms(3)[symmetric] nft_accept_def)
  obtain as'' e where as'_def: "as' = as'' @ [e]" "e = End_Sim \<or> e = End_Copy"
    "End_Copy \<notin> set as''" "End_Sim \<notin> set as''"
    using nft_comp_Accept'[OF comp q'_not_Init_Accept(2) q''_def]
      nft_comp_End_Sim[OF comp] nft_comp_End_Copy[OF comp]
    by auto
  obtain qb qbs''' where qbs'_def: "qbs' = qb # qbs'''" "nft_step Init a qb"
    "nft.computation_ext (fst qb) (as', qbs''') f'"
    using assms(3) lassms(2)
    by (cases qbs') (auto elim: nft.computation_ext.cases)
  have fst_qb_mode: "fst qb = Copy \<or> fst qb = PreStep None"
    using qbs'_def(2)
    by (auto elim: nft_step.cases)
  obtain r bs' bs'' where split: "nft.computation q' (as'', bs') r"
    "nft_step r e (q'', bs'')"
    using nft.computation_split[OF comp[unfolded as'_def(1)]]
    by (auto dest: nft.step_dest)
  obtain r' cs' cs'' where split': "nft.computation (fst qb) (as'', cs') r'"
    "nft_step r' e (f', cs'')"
    using nft.computation_split[OF nft.computation_ext_sound[OF qbs'_def(3), unfolded as'_def(1)]]
    by (auto dest: nft.step_dest)
  have "fst qb = q'"
    using as'_def(2)
  proof (rule disjE)
    assume e_def: "e = End_Sim"
    have r_r'_def: "r = PreStep None" "r' = PreStep None"
      using split(2) split'(2)
      by (auto simp: e_def elim: nft_step.cases)
    have q'_def: "q' = PreStep None"
      using split(1) q'_mode r_r'_def(1) nft_comp_Copy_PreStep
      by auto
    have fst_qb_def: "fst qb = PreStep None"
      using split'(1) fst_qb_mode r_r'_def(2) nft_comp_Copy_PreStep
      by auto
    show "fst qb = q'"
      by (auto simp: q'_def fst_qb_def)
  next
    assume e_def: "e = End_Copy"
    have r_r'_def: "r = Copy" "r' = Copy"
      using split(2) split'(2)
      by (auto simp: e_def elim: nft_step.cases)
    have q'_def: "q' = Copy"
      using split(1) q'_mode r_r'_def(1) nft_comp_PreStep_Copy
      by auto
    have fst_qb_def: "fst qb = Copy"
      using split'(1) fst_qb_mode r_r'_def(2) nft_comp_PreStep_Copy
      by auto
    show "fst qb = q'"
      by (auto simp: q'_def fst_qb_def)
  qed
  then have qb_def: "qb = (q', bs)"
    using fst_step qbs'_def(2)
    by (auto elim!: nft_step.cases)
  have comp': "nft.computation_ext q' (as', qbs''') f'"
    using qbs'_def(3)
    by (auto simp: qb_def)
  show "qbs = qbs'"
    using lassms(2) unambiguous_aux[OF lassms(5) comp' q'_not_Init_Accept(1)]
    by (auto simp: qbs'_def(1) qb_def)
qed

(* Claim 15 *)
interpretation uNFT Init nft_step nft_accept UNIV
  using unambiguous
  by unfold_locales assumption

(* Claim 16 *)
lemma unbounded_iff_reachable: "\<not>(\<exists>K. nft.bounded K) \<longleftrightarrow> (\<forall>n. \<exists>cs. reachable cs \<and> length cs \<ge> n)"
  using reachable_then_unbounded unbounded_then_reachable
  by auto

end

end
