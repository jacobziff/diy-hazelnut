open Sexplib.Std;
// open Monad_lib.Monad; // Uncomment this line to use the maybe monad

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

// A.2.2
let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(h: Hexp.t) => h // EETop
  | Lam(s: string, z: Zexp.t) => Lam(s, erase_exp(z)) // EELam
  | LAp(z: Zexp.t, h: Hexp.t) => Ap(erase_exp(z), h) // EEAPL
  | RAp(h: Hexp.t, z: Zexp.t) => Ap(h, erase_exp(z)) // EEAPR
  | LPlus(z: Zexp.t, h: Hexp.t) => Plus(erase_exp(z), h) // EEPlusL
  | RPlus(h: Hexp.t, z: Zexp.t) => Plus(h, erase_exp(z)) // EEPlusR
  | LAsc(z: Zexp.t, t: Htyp.t) => Asc(erase_exp(z), t) // EEAscL
  | RAsc(h: Hexp.t, z: Ztyp.t) => Asc(h, erase_typ(z)) // EEAscR
  | NEHole(z: Zexp.t) => NEHole(erase_exp(z)) // EENEHole
  };
}

// A.2.1
and erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(h: Htyp.t) => h // ETTop
  | LArrow(z: Ztyp.t, h: Htyp.t) => Arrow(erase_typ(z), h) // ETArrL
  | RArrow(h: Htyp.t, z: Ztyp.t) => Arrow(h, erase_typ(z)) // ETArrR
  };
};

// A.1.1
let rec compatible = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Htyp.Hole, _) => true // TCHole2
  | (_, Htyp.Hole) => true // TCHole1
  | (Htyp.Arrow(t1i, t1o), Htyp.Arrow(t2i, t2o)) =>
    // TCarr
    compatible(t1i, t2i) && compatible(t1o, t2o)
  | (Htyp.Arrow(_, _), Htyp.Num) => false // ICNumArr2
  | (Htyp.Num, Htyp.Arrow(_, _)) => false // ICNumArr1
  | _ => t1 == t2 // TCRefl, ICArr1, ICArr2
  };
}

// A.1.2
and match = (t: Htyp.t): Htyp.t => {
  switch (t) {
  | Htyp.Hole => Htyp.Arrow(Htyp.Hole, Htyp.Hole) // MAHole
  | Htyp.Arrow(tin, tout) => Htyp.Arrow(tin, tout) // MAArr
  | _ => Htyp.Hole // Essentially "None," but without the need for an option type
  };
};

// A.1.3
let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(s: string) =>
    // SVar
    switch (TypCtx.find(s, ctx)) {
    | item => Some(item)
    | exception _ => None
    }
  | Lam(_: string, _: Hexp.t) => None // There is no type synthesis rule that applies to this form, so lambda abstractions can appear only in analytic position, i.e. where an expected type is known.
  | Ap(f: Hexp.t, x: Hexp.t) =>
    // SAp
    let t1 = syn(ctx, f);
    switch (t1) {
    | None => None
    | Some(t1) =>
      switch (match(t1)) {
      | Htyp.Arrow(t2, tprime) =>
        if (ana(ctx, x, t2)) {
          Some(tprime);
        } else {
          None;
        }
      | _ => None
      }
    };
  | Lit(_: int) => Some(Htyp.Num) // SNum
  | Plus(l: Hexp.t, r: Hexp.t) =>
    // SPlus
    if (ana(ctx, l, Htyp.Num) && ana(ctx, r, Htyp.Num)) {
      Some(Htyp.Num);
    } else {
      None;
    }
  | Asc(h: Hexp.t, t: Htyp.t) =>
    // SAsc
    if (ana(ctx, h, t)) {
      Some(t);
    } else {
      None;
    }
  | EHole => Some(Htyp.Hole) // SHole
  | NEHole(h: Hexp.t) =>
    // SNEHole
    switch (syn(ctx, h)) {
    | None => None
    | _ => Some(Htyp.Hole)
    }
  };
}

// A.1.3
and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(x: string, h: Hexp.t) =>
    // ALam
    switch (match(t)) {
    | Htyp.Arrow(t1, t2) => ana(TypCtx.add(x, t1, ctx), h, t2)
    | _ => false
    }
  | _ =>
    // ASubsume
    switch (syn(ctx, e)) {
    | Some(item) => compatible(t, item)
    | None => false
    }
  };
};

// A.3.3
let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  switch (e, t, a) {
  | (_, _, Move(d: Dir.t)) =>
    // SAMove
    switch (exp_action(e, d)) {
    | Some(z) => Some((z, t))
    | _ => None
    }
  | (Cursor(h), _, Construct(Asc)) => Some((RAsc(h, Cursor(t)), t)) // SAConAsc
  | (Cursor(EHole), Hole, Construct(Var(x: string))) =>
    Some((Cursor(Var(x)), TypCtx.find(x, ctx))) // SAConVar
  | (Cursor(EHole), Hole, Construct(Lam(x: string))) =>
    // SAConLam
    Some((
      RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  | (Cursor(h), _, Construct(Ap)) =>
    switch (match(t)) {
    | Htyp.Hole =>
      // SaConAPOtw
      if (compatible(t, Htyp.Arrow(Htyp.Hole, Htyp.Hole))) {
        None;
      } else {
        Some((RAp(NEHole(h), Cursor(EHole)), Htyp.Hole));
      }
    | Htyp.Arrow(_: Htyp.t, t2: Htyp.t) =>
      Some((RAp(h, Cursor(EHole)), t2)) // SAConAPArr
    | _ => None
    }
  | (Cursor(EHole), Hole, Construct(Lit(n: int))) =>
    Some((Cursor(Lit(n)), Num)) // SAConNumLit
  | (Cursor(h), _, Construct(Plus)) =>
    if (compatible(t, Htyp.Num)) {
      // SAConPlus1
      Some((RPlus(h, Cursor(EHole)), Htyp.Num));
    } else {
      // SAConPlus2
      Some((RPlus(NEHole(h), Cursor(EHole)), Htyp.Num));
    }
  | (Cursor(h), _, Construct(NEHole)) => Some((NEHole(Cursor(h)), Hole)) // SAConNEHole
  | (Cursor(_: Hexp.t), _, Del) => Some((Cursor(EHole), t)) // SADel
  | (Cursor(NEHole(h: Hexp.t)), Hole, Finish) =>
    // SAFinish
    switch (syn(ctx, h)) {
    | Some(t') => Some((Cursor(h), t'))
    | _ => None
    }
  | (LAsc(e, t'), _, _) =>
    // SAZipAsc1
    if (t == t') {
      switch (ana_action(ctx, e, a, t)) {
      | Some(z) => Some((LAsc(z, t), t))
      | _ => None
      };
    } else {
      None;
    }
  | (RAsc(e, t1), _, _) =>
    // SAZipAsc2
    switch (typ_action(t1, a)) {
    | Some(t') =>
      if (ana(ctx, e, erase_typ(t'))) {
        Some((Zexp.RAsc(e, t'), erase_typ(t')));
      } else {
        None;
      }
    | _ => None
    }
  | (LAp(e1, e2), _, _) =>
    // SaZipApArr
    switch (syn(ctx, erase_exp(e1))) {
    | Some(t2) =>
      switch (syn_action(ctx, (e1, t2), a)) {
      | Some((e', t3)) =>
        switch (match(t3)) {
        | Arrow(t4, t5) =>
          if (ana(ctx, e2, t4)) {
            Some((LAp(e', e2), t5));
          } else {
            None;
          }
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | (RAp(e1, e2), _, _) =>
    // SaZipApAna
    switch (syn(ctx, e1)) {
    | Some(t2) =>
      switch (match(t2)) {
      | Arrow(t3, t4) =>
        switch (ana_action(ctx, e2, a, t3)) {
        | Some(e') => Some((RAp(e1, e'), t4))
        | _ => None
        }
      | _ => None
      }
    | _ => None
    }
  | (LPlus(e1, e2), Num, _) =>
    // SaZipPlus1
    switch (ana_action(ctx, e1, a, Num)) {
    | Some(e') => Some((LPlus(e', e2), Num))
    | _ => None
    }
  | (RPlus(e1, e2), Num, _) =>
    // SaZipPlus2
    switch (ana_action(ctx, e2, a, Num)) {
    | Some(e') => Some((RPlus(e1, e'), Num))
    | _ => None
    }
  | (NEHole(e'), Hole, _) =>
    // SaZipHole
    switch (syn(ctx, erase_exp(e'))) {
    | Some(t') =>
      switch (syn_action(ctx, (e', t'), a)) {
      | Some((z, _)) => Some((NEHole(z), Hole))
      | _ => None
      }
    | _ => None
    }
  | _ => None
  };
}

// A.3.3
and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (e, match(t)) {
  | (Lam(x, e1), Arrow(t1, t2)) =>
    // AAZipLam
    switch (ana_action(TypCtx.add(x, t1, ctx), e1, a, t2)) {
    | Some(z) => Some(Lam(x, z))
    | _ => None
    }
  | _ =>
    switch (a) {
    | Move(d: Dir.t) => exp_action(e, d) // AAMove
    | Construct(s: Shape.t) =>
      switch (s) {
      | Asc =>
        // AAConAsc
        switch (e) {
        | Cursor(h) => Some(RAsc(h, Cursor(t)))
        | _ => None
        }
      | Var(x: string) =>
        // AAConVar
        switch (e) {
        | Cursor(EHole) => Some(NEHole(Cursor(Var(x))))
        | _ => None
        }
      | Lam(x: string) =>
        switch (match(t)) {
        | Hole =>
          // AAConLam2
          switch (e) {
          | Cursor(EHole) =>
            if (compatible(t, Arrow(Hole, Hole))) {
              None;
            } else {
              Some(
                NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))),
              );
            }
          | _ => None
          }
        | Arrow(_, _) =>
          // AAConLam1
          switch (e) {
          | Cursor(EHole) => Some(Lam(x, Cursor(EHole)))
          | _ => None
          }
        | _ => None
        }
      | Lit(n: int) =>
        // AAConNumLit
        switch (e) {
        | Cursor(EHole) =>
          if (compatible(t, Htyp.Num)) {
            None;
          } else {
            Some(NEHole(Cursor(Lit(n))));
          }
        | _ => None
        }
      | _ =>
        // AASubsume
        let t1 = syn(ctx, erase_exp(e));
        switch (t1) {
        | Some(t1) =>
          let res = syn_action(ctx, (e, t1), a);
          switch (res) {
          | Some((z, t2)) =>
            if (compatible(t1, t2)) {
              Some(z);
            } else {
              None;
            }
          | _ => None
          };
        | _ => None
        };
      }
    | Del =>
      switch (e) {
      | Cursor(_: Hexp.t) => Some(Cursor(EHole)) // AADel
      | _ => None
      }
    | Finish =>
      switch (e) {
      | Cursor(NEHole(h: Hexp.t)) =>
        // AAFinish
        let t' = ana(ctx, h, t);
        if (t') {
          Some(Cursor(h));
        } else {
          None;
        };
      | _ => None
      }
    }
  };
}

// A.3.1
and typ_action = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  switch (t, a) {
  | (Cursor(Arrow(t1, t2)), Move(Child(One))) =>
    Some(LArrow(Cursor(t1), t2)) // TMArrChild1
  | (Cursor(Arrow(t1, t2)), Move(Child(Two))) =>
    Some(RArrow(t1, Cursor(t2))) // TMArrChild2
  | (LArrow(Cursor(t1), t2), Move(Parent)) => Some(Cursor(Arrow(t1, t2))) // TMArrParent1
  | (RArrow(t1, Cursor(t2)), Move(Parent)) => Some(Cursor(Arrow(t1, t2))) // TMArrParent2
  | (Cursor(_), Del) => Some(Cursor(Hole)) // TMDel
  | (Cursor(t), Construct(Arrow)) => Some(RArrow(t, Cursor(Hole))) // TMConArrow
  | (Cursor(Hole), Construct(Num)) => Some(Cursor(Num)) // TMConNum
  | (LArrow(t1, t2), _) =>
    // TMArrZip1
    switch (typ_action(t1, a)) {
    | Some(t1') => Some(LArrow(t1', t2))
    | _ => None
    }
  | (RArrow(t1, t2), _) =>
    // TMArrZip2
    switch (typ_action(t2, a)) {
    | Some(t2') => Some(RArrow(t1, t2'))
    | _ => None
    }
  | _ => None
  };
}

// A.3.2
and exp_action = (e: Zexp.t, d: Dir.t): option(Zexp.t) => {
  switch (e, d) {
  | (Cursor(Asc(e: Hexp.t, t: Htyp.t)), Child(One)) =>
    Some(LAsc(Cursor(e), t)) // EMAscChild1
  | (Cursor(Asc(e: Hexp.t, t: Htyp.t)), Child(Two)) =>
    Some(RAsc(e, Cursor(t))) // EMAscChild2
  | (LAsc(Cursor(e: Hexp.t), t: Htyp.t), Parent) =>
    Some(Cursor(Asc(e, t))) // EMAscParent1
  | (RAsc(e: Hexp.t, Cursor(t: Htyp.t)), Parent) =>
    Some(Cursor(Asc(e, t))) // EMAscParent1
  | (Cursor(Lam(x: string, e: Hexp.t)), Child(One)) =>
    Some(Lam(x, Cursor(e))) // EMLamChild1
  | (Lam(x: string, Cursor(e: Hexp.t)), Parent) =>
    Some(Cursor(Lam(x, e))) // EMParent
  | (Cursor(Plus(e1: Hexp.t, e2: Hexp.t)), Child(One)) =>
    Some(LPlus(Cursor(e1), e2)) // EMPlusChild1
  | (Cursor(Plus(e1: Hexp.t, e2: Hexp.t)), Child(Two)) =>
    Some(RPlus(e1, Cursor(e2))) // EMPlusChild2
  | (LPlus(Cursor(e1: Hexp.t), e2: Hexp.t), Parent) =>
    Some(Cursor(Plus(e1, e2))) // EMPlusParent1
  | (RPlus(e1: Hexp.t, Cursor(e2: Hexp.t)), Parent) =>
    Some(Cursor(Plus(e1, e2))) // EMPlusParent2
  | (Cursor(Ap(e1: Hexp.t, e2: Hexp.t)), Child(One)) =>
    Some(LAp(Cursor(e1), e2)) // EMApChild1
  | (Cursor(Ap(e1: Hexp.t, e2: Hexp.t)), Child(Two)) =>
    Some(RAp(e1, Cursor(e2))) // EMApChild2
  | (LAp(Cursor(e1: Hexp.t), e2: Hexp.t), Parent) =>
    Some(Cursor(Ap(e1, e2))) // EMApParent1
  | (RAp(e1: Hexp.t, Cursor(e2: Hexp.t)), Parent) =>
    Some(Cursor(Ap(e1, e2))) // EMApParent2
  | (Cursor(NEHole(h: Hexp.t)), Child(One)) => Some(NEHole(Cursor(h))) // EMNEHoleChild1
  | (NEHole(Cursor(h: Hexp.t)), Parent) => Some(Cursor(NEHole(h))) // EMNEHoleParent
  | _ => None
  };
};
