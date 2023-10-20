// -gobra

package wip

type timestamp struct {
	time int64
	val  int64
}

// @ requires p > 0 && acc(ts.mem(), p)
// @ pure
func (ts *timestamp) ToComparable( /* @ghost p perm @*/ ) int64 {
	return /*@unfolding ts.mem() in @*/ ts.val
}

/*@
pred (ts *timestamp) mem() {
	acc(ts)
}
@*/

type Elem = (*timestamp)

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

type timestampSet map[int64]Elem

// @ ensures res != nil && res.mem()
func MkSet() (res Set) {
	m /*@@@*/ := make(timestampSet)
	// @ fold m.mem()
	return &m
}

// @ preserves p0 > 0 && p1 > 0 && acc(s, p0) && acc(*s, p0) && acc(val.mem(), p1)
func (s *timestampSet) Has(val Elem /*@, ghost p0, p1 perm @*/) (res Elem) {
	if val != nil {
		return (*s)[val.ToComparable( /*@ p1 @*/ )]
	}
	return nil
}

// @ preserves p > 0 && acc(s, p) && acc(*s, p)
func (s *timestampSet) HasKey(key int64 /*@, ghost p perm @*/) (res Elem) {
	return (*s)[key]
}

// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *timestampSet) Add(val Elem /*@, ghost p perm @*/) {
	if val != nil {
		(*s)[val.ToComparable( /*@ p @*/ )] = val
	}
}

// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *timestampSet) Rm(val Elem /*@, ghost p perm @*/) (res Elem) {
	if val != nil {
		e := (*s)[val.ToComparable( /*@ p @*/ )]
		s.DoDeleteElem(val.ToComparable( /*@ p @*/ ))
		return e
	}
	return nil
}

// @ pure
// @ requires p > 0 && acc(s, p) && acc(*s, p)
// @ ensures 0 <= res
func (s *timestampSet) Size( /*@ ghost p perm @*/ ) (res int) {
	return len(*s)
}

// @ trusted
// @ preserves acc(s) && acc(*s)
func (s *timestampSet) DoDeleteElem(key int64) {
	delete((*s), key)
}

/*@
pred (s *timestampSet) mem() {
  acc(s) && acc(*s)
}
@*/

/*@
(*timestampSet) implements Set{

  (s *timestampSet) Has(val Elem, ghost p0 perm, ghost p1 perm) (res Elem) {
	unfold acc(s.mem(), p0)
	res = s.Has(val, p0, p1)
	fold acc(s.mem(), p0)
  }

  (s *timestampSet) HasKey(key int64, ghost p perm) (res Elem) {
	unfold acc(s.mem(), p)
	res = s.HasKey(key, p)
	fold acc(s.mem(), p)
  }

  (s *timestampSet) Add(val Elem, ghost p perm) () {
	unfold s.mem()
	s.Add(val, p)
	fold s.mem()
  }

  (s *timestampSet) Rm(val Elem, ghost p perm) (res Elem) {
	unfold s.mem()
	res = s.Rm(val, p)
	fold s.mem()
  }

  pure (s *timestampSet) Size(ghost p perm) (int) {
	return unfolding acc(s.mem(), p) in s.Size(p)
  }
}
@*/
