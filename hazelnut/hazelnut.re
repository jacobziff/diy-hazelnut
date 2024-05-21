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

let erase_exp = (e: Zexp.t): Hexp.t => {
  // Used to suppress unused variable warnings
  switch (e) {
  | Cursor(h: Hexp.t) => h
  | Lam(_: string, _: Zexp.t) => raise(Unimplemented)
  | LAp(_: Zexp.t, h: Hexp.t) => h
  | RAp(h: Hexp.t, _: Zexp.t) => h
  | LPlus(_: Zexp.t, h: Hexp.t) => h
  | RPlus(h: Hexp.t, _: Zexp.t) => h
  | LAsc(_: Zexp.t, _: Htyp.t) => raise(Unimplemented)
  | RAsc(h: Hexp.t, _: Ztyp.t) => h
  | NEHole(_: Zexp.t) => raise(Unimplemented)
  };
};

let rec compatible = (t1: Htyp.t, t2: Htyp.t): bool => {
  switch (t1, t2) {
  | (Htyp.Hole, _) => true
  | (_, Htyp.Hole) => true
  | (Htyp.Arrow(t1i, t1o), Htyp.Arrow(t2i, t2o)) =>
    compatible(t1i, t2i) && compatible(t1o, t2o)
  | (Htyp.Arrow(_, _), Htyp.Num) => false
  | (_, Htyp.Arrow(_, Htyp.Num)) => false
  | _ => t1 == t2
  };
}

and match = (t: Htyp.t): Htyp.t => {
  switch (t) {
  | Htyp.Hole => Htyp.Arrow(Htyp.Hole, Htyp.Hole)
  | Htyp.Arrow(tin, tout) => Htyp.Arrow(tin, tout)
  | _ => Htyp.Hole // Essentially "None," but without the need for an option type
  };
};

let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Var(s: string) =>
    switch (TypCtx.find(s, ctx)) {
    | item => Some(item)
    | exception _ => None
    }
  | Lam(_: string, _: Hexp.t) => raise(Unimplemented)
  | Ap(f: Hexp.t, x: Hexp.t) =>
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
  | Lit(_: int) => Some(Htyp.Num)
  | Plus(l: Hexp.t, r: Hexp.t) =>
    if (ana(ctx, l, Htyp.Num) && ana(ctx, r, Htyp.Num)) {
      Some(Htyp.Num);
    } else {
      None;
    }
  | Asc(_: Hexp.t, _: Htyp.t) => raise(Unimplemented)
  | EHole => Some(Htyp.Hole)
  | NEHole(h: Hexp.t) =>
    switch (syn(ctx, h)) {
    | None => None
    | _ => Some(Htyp.Hole)
    }
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (e) {
  | Lam(_: string, _: Hexp.t) => raise(Unimplemented)
  | _ =>
    switch (syn(ctx, e)) {
    | Some(item) => compatible(t, item)
    | None => false
    }
  };
};

let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  switch (a) {
  | Move(_: Dir.t) => raise(Unimplemented)
  | Construct(_: Shape.t) => raise(Unimplemented)
  | Del => raise(Unimplemented)
  | Finish => raise(Unimplemented)
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;
  switch (a) {
  | Move(_: Dir.t) => raise(Unimplemented)
  | Construct(_: Shape.t) => raise(Unimplemented)
  | Del => raise(Unimplemented)
  | Finish => raise(Unimplemented)
  };
};
