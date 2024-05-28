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

and erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(h: Htyp.t) => h // ETTop
  | LArrow(z: Ztyp.t, h: Htyp.t) => Arrow(erase_typ(z), h) // ETArrL
  | RArrow(h: Htyp.t, z: Ztyp.t) => Arrow(h, erase_typ(z)) // ETArrR
  };
};

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

and match = (t: Htyp.t): Htyp.t => {
  switch (t) {
  | Htyp.Hole => Htyp.Arrow(Htyp.Hole, Htyp.Hole) // MAHole
  | Htyp.Arrow(tin, tout) => Htyp.Arrow(tin, tout) // MAArr
  | _ => Htyp.Hole // Essentially "None," but without the need for an option type
  };
};

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

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  switch (a) {
  // | Zipper Cases? raise(Unimplemented)
  | Move(_: Dir.t) => raise(Unimplemented)
  | Construct(s: Shape.t) =>
    switch (s) {
    | Arrow => raise(Unimplemented)
    | Num => raise(Unimplemented)
    | Asc =>
      // SaConAsc
      switch (e) {
      | Cursor(h) => Some((RAsc(h, Cursor(t)), t))
      | _ => None
      }
    | Var(x: string) =>
      // SAConVar
      switch (e, t) {
      | (Cursor(EHole), Htyp.Hole) =>
        Some((Cursor(Var(x)), TypCtx.find(x, ctx)))
      | _ => None
      }
    | Lam(x: string) =>
      // SaConLam
      switch (e, t) {
      | (Cursor(EHole), Hole) =>
        Some((
          RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
          Arrow(Hole, Hole),
        ))
      | _ => None
      }
    | Ap =>
      switch (match(t)) {
      | Htyp.Hole =>
        // SaConAPOtw
        if (compatible(t, Htyp.Arrow(Htyp.Hole, Htyp.Hole))) {
          None;
        } else {
          switch (e) {
          | Cursor(h: Hexp.t) =>
            Some((RAp(NEHole(h), Cursor(EHole)), Htyp.Hole))
          | _ => None
          };
        }
      | Htyp.Arrow(_: Htyp.t, t2: Htyp.t) =>
        // SAConAPArr
        switch (e) {
        | Cursor(h: Hexp.t) => Some((RAp(h, Cursor(EHole)), t2))
        | _ => None
        }
      | _ => None
      }
    | Lit(n: int) =>
      // SAConNumLit
      switch (e, t) {
      | (Cursor(EHole), Hole) => Some((Cursor(Lit(n)), Num))
      | _ => None
      }
    | Plus =>
      if (compatible(t, Htyp.Num)) {
        // SAConPlus1
        switch (e) {
        | Cursor(h) => Some((RPlus(h, Cursor(EHole)), Htyp.Num))
        | _ => None
        };
      } else {
        // SAConPlus2
        switch (e) {
        | Cursor(h) => Some((RPlus(NEHole(h), Cursor(EHole)), Htyp.Num))
        | _ => None
        };
      }
    | NEHole =>
      // SAConNEHole
      switch (e) {
      | Cursor(h) => Some((NEHole(Cursor(h)), Hole))
      | _ => None
      }
    }
  | Del =>
    switch (e) {
    | Cursor(_: Hexp.t) => Some((Cursor(EHole), t)) // SADel
    | _ => None
    }
  | Finish =>
    switch (e, t) {
    | (Cursor(NEHole(h: Hexp.t)), Hole) =>
      // SAFinish
      switch (syn(ctx, h)) {
      | Some(t') => Some((Cursor(h), t'))
      | _ => None
      }
    | _ => None
    }
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (a) {
  // | Zipper Cases? raise(Unimplemented)
  | Move(_: Dir.t) => raise(Unimplemented)
  | Construct(s: Shape.t) =>
    switch (s) {
    | Arrow => raise(Unimplemented)
    | Num => raise(Unimplemented)
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
    | Ap => None
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
    | Plus => None
    | NEHole => None
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
  };
};
