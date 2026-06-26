package example

type S struct{ f, g int }

//@ pred Fields(x *S) { acc(&x.f) && acc(&x.g) && (x.f <= x.g) }
//@ pred Packed(x *S) { Fields(x) }

// Example
// @ requires acc(&a.f) && acc(&a.g)
// @ ensures acc(Packed(a))
func foo(a *S) {
	if a.f > a.g {
		a.f, a.g = a.g, a.f
	}

	//@ assert acc(Packed(a))
}
