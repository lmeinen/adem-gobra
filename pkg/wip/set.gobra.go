package wip

type Elem interface {
	// @ pred mem()

	// @ requires acc(mem(), _)
	// @ pure
	ToComparable() (res int64)
}

type Set interface {
	// @ pred mem()

	// @ ghost-parameters: p0 perm, p1 perm
	// @ preserves p0 > 0 && p1 > 0 && acc(mem(), p0) && acc(val.mem(), p1)
	Has(val Elem) (res Elem)

	// @ ghost-parameters: p perm
	// @ preserves p > 0 && acc(mem(), p)
	HasKey(key int64) (res Elem)

	// @ ghost-parameters: p perm
	// @ preserves mem() && p > 0 && acc(val.mem(), p)
	Add(val Elem)

	// @ ghost-parameters: p perm
	// @ preserves mem() && p > 0 && acc(val.mem(), p)
	Rm(val Elem) (res Elem)

	// @ ghost-parameters: p perm
	// @ requires p > 0 && acc(mem(), p)
	// @ pure
	Size() int
}

type int64Set map[int64]Elem

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
    return unfolding acc(s.mem()) in s.Size(p)
  }
}
@*/

func MkSet() Set {
	m := make(int64Set) // @ addressable: m
	return &m
}

// @ ghost-parameters: p0 perm, p1 perm
// @ preserves p0 > 0 && p1 > 0 && acc(s, p0) && acc(*s, p0) && acc(val.mem(), p1)
func (s *int64Set) Has(val Elem) (res Elem) {
	if val != nil {
		return (*s)[val.ToComparable()]
	}
	return nil
}

// @ ghost-parameters: p perm
// @ preserves p > 0 && acc(s, p) && acc(*s, p)
func (s *int64Set) HasKey(key int64) (res Elem) {
	return (*s)[key]
}

// @ ghost-parameters: p perm
// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *int64Set) Add(val Elem) {
	if val != nil {
		(*s)[val.ToComparable()] = val
	}
}

// @ ghost-parameters: p perm
// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *int64Set) Rm(val Elem) (res Elem) {
	if val != nil {
		e := (*s)[val.ToComparable()]
		s.DoDeleteElem(val) /*@ with: p @*/
		return e
	}
	return nil
}

// @ ghost-parameters: p perm
// @ pure
// @ requires p > 0 && acc(s, p) && acc(*s, p)
func (s *int64Set) Size() int {
	return len(*s)
}

// @ ghost-parameters: p perm
// @ trusted
// @ requires val != nil
// @ preserves acc(s) && acc(*s) && p > 0 && acc(val.mem(), p)
func (s *int64Set) DoDeleteElem(val Elem) {
	delete((*s), val.ToComparable())
}
