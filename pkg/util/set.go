package util

type Elem interface {
	// @ pred mem()

	// @ requires acc(mem(), _)
	// @ pure
	ToComparable() (res int64)
}

type Set interface {
	// @ pred mem()

	// @ preserves p0 > 0 && p1 > 0 && acc(mem(), p0) && acc(val.mem(), p1)
	Has(val Elem /*@, ghost p0, p1 perm @*/) (res Elem)

	// @ preserves p > 0 && acc(mem(), p)
	HasKey(key int64 /*@, ghost p perm @*/) (res Elem)

	// @ preserves mem() && p > 0 && acc(val.mem(), p)
	Add(val Elem /*@, ghost p perm @*/)

	// @ preserves mem() && p > 0 && acc(val.mem(), p)
	Rm(val Elem /*@, ghost p perm @*/) (res Elem)

	// @ requires p > 0 && acc(mem(), p)
	// @ ensures 0 <= res
	// @ pure
	Size( /*@ ghost p perm @*/ ) (res int)
}

type int64Set map[int64]Elem

func MkSet() Set {
	i64Set := make(int64Set) // @ addressable: i64Set
	return &i64Set
}

// @ preserves p0 > 0 && p1 > 0 && acc(s, p0) && acc(*s, p0) && acc(val.mem(), p1)
func (s *int64Set) Has(val Elem /*@, ghost p0, p1 perm @*/) (res Elem) {
	if val != nil {
		return (*s)[val.ToComparable()]
	}
	return nil
}

// @ preserves p > 0 && acc(s, p) && acc(*s, p)
func (s *int64Set) HasKey(key int64 /*@, ghost p perm @*/) (res Elem) {
	return (*s)[key]
}

// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *int64Set) Add(val Elem /*@, ghost p perm @*/) {
	if val != nil {
		(*s)[val.ToComparable()] = val
	}
}

// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *int64Set) Rm(val Elem /*@, ghost p perm @*/) (res Elem) {
	if val != nil {
		e := (*s)[val.ToComparable()]
		s.DoDeleteElem(val.ToComparable())
		return e
	}
	return nil
}

// @ pure
// @ requires p > 0 && acc(s, p) && acc(*s, p)
// @ ensures 0 <= res
func (s *int64Set) Size( /*@ ghost p perm @*/ ) (res int) {
	return len(*s)
}

// @ trusted
// @ preserves acc(s) && acc(*s)
func (s *int64Set) DoDeleteElem(key int64) {
	delete((*s), key)
}

/*@
pred (s *int64Set) mem() {
  acc(s) && acc(*s)
}
@*/

/*@
(*int64Set) implements Set{

  (s *int64Set) Has(val Elem, ghost p0 perm, ghost p1 perm) (res Elem) {
	unfold acc(s.mem(), p0)
	res = s.Has(val, p0, p1)
	fold acc(s.mem(), p0)
  }

  (s *int64Set) HasKey(key int64, ghost p perm) (res Elem) {
	unfold acc(s.mem(), p)
	res = s.HasKey(key, p)
	fold acc(s.mem(), p)
  }

  (s *int64Set) Add(val Elem, ghost p perm) () {
	unfold s.mem()
	s.Add(val, p)
	fold s.mem()
  }

  (s *int64Set) Rm(val Elem, ghost p perm) (res Elem) {
	unfold s.mem()
	res = s.Rm(val, p)
	fold s.mem()
  }

  pure (s *int64Set) Size(ghost p perm) (int) {
	return unfolding acc(s.mem(), p) in s.Size(p)
  }
}
@*/
