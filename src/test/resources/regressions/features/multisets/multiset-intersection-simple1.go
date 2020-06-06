package pkg

func example1(ghost m1 mset[int], ghost m2 mset[int]) {
  ghost m := m1 intersection m2
}

ghost func example2(m1 mset[int], m2 mset[int]) (m mset[int]) {
  m = m1 intersection m2
}

ensures m == m1 intersection m2
func example3(ghost m1 mset[int], ghost m2 mset[int]) (ghost m mset[int]) {
  m = m1 intersection m2
}

func example4(ghost m1 mset[int], ghost m2 mset[int], ghost m3 mset[int]) {
  assert (m1 intersection m2) intersection m3 == m1 intersection (m2 intersection m3)
}

func example5(ghost m1 mset[int], ghost m2 mset[int]) {
  assert m1 intersection m2 == m2 intersection m1
}

func example6() {
  assert mset[int] { 1, 2 } union mset[int] { 3 } == mset[int] { 1, 2, 3 }
  assert mset[int] { 1, 2 } union mset[int] { 2, 3 } == mset[int] { 1, 2, 2, 3 }
}

func example7(ghost m mset[int]) {
  assert m == m union mset[int] { }
  assert m union m == m ==> m == mset[int] { }
}

func example8(ghost m mset[int]) {
  assert m intersection m == m
  assert m intersection mset[int] { } == mset[int] { }
}