export const FieldModulusWGSL = 
`
alias Field = u256;

fn addc(a: u32, b: u32, car: u32) -> vec2<u32> {
  let x = u64from32(a);
  let y = u64from32(b);
  let carry = u64from32(car);

  var res = u64add(x, y);
  res = u64add(res, carry);

  return vec2<u32>(res.lo, res.hi);
}

fn subb(a: u32, b: u32, bor: u32) -> vec2<u32> {
  let x = u64from32(a);
  let y = u64from32(b);

  let sb = bor >> 31;
  let borrow = u64from32(sb);

  var res = u64sub(x, y);
  res = u64sub(res, borrow);

  return vec2<u32>(res.lo, res.hi);
}

fn mac(a: u32, b: u32, c: u32, car: u32) -> vec2<u32> {
  let x = u64from32(a);
  let y = u64from32(b);
  let z = u64from32(c);
  let carry = u64from32(car);

  var res = u64mul(y, z);
  res = u64add(res, x);
  res = u64add(res, carry);

  return vec2<u32>(res.lo, res.hi);
}

fn field_add(x: u256, y: u256) -> u256 {
  var carry = u32(0);
  var res: u256;

  for (var i = 7i; i >= 0i; i--) {
      let v = addc(x.components[i], y.components[i], carry);
      res.components[i] = v[0];
      carry = v[1];
  }

  var borrow = u32(0);
  for (var i = 7i; i >= 0i; i--) {
      let v = subb(res.components[i], N.components[i], borrow);
      res.components[i] = v[0];
      borrow = v[1];
  }

  if (carry == 0 && borrow != 0) {
      for (var i = 7i; i >= 0i; i--) {
          let v = addc(res.components[i], N.components[i], carry);
          res.components[i] = v[0];
          carry = v[1];
      }
  }

  return res;
}

fn mont_mul(x: u256, y: u256) -> u256 {
  var carry = u32(0);
  var borrow = u32(0);
  var k = u32(0);
  var t: array<u32, 10>;
  var res: u256;

  for (var i = 0i; i < 8i; i++) {
      carry = 0;
      for (var j = 0i; j < 8i; j++) {
          let v = mac(t[j], x.components[7-i], y.components[7-j], carry);
          t[j] = v[0];
          carry = v[1];
      }
      var v = addc(t[8], carry, 0);
      t[8] = v[0];
      t[9] = v[1];

      carry = 0;
      k = t[0] * r_inv;

      v = mac(t[0], k, N.components[7], 0);
      carry = v[1];

      for (var j = 0i; j < 7i; j++) {
          let v = mac(t[j+1], k, N.components[6-j], carry);
          t[j] = v[0];
          carry = v[1];
      }

      v = addc(carry, t[8], 0);
      t[7] = v[0];
      carry = v[1];

      t[8] = t[9] + carry;
  }

  borrow = 0;
  for (var i = 0i; i < 8i; i++) {
      let v = subb(t[i], N.components[7-i], borrow);
      res.components[7-i] = v[0];
      borrow = v[1];
  }

  borrow = borrow ^ (u32(0) - t[8]);

  carry = 0;
  for (var i = 0i; i < 8i; i++) {
      let v = addc(res.components[7-i], N.components[7-i]&borrow, carry);
      res.components[7-i] = v[0];
      carry = v[1];
  }

  return res;
}

fn to_mont(x: u256) -> u256 {
  return mont_mul(x, R_Squared);
}

fn from_mont(x: u256) -> u256 {
  return mont_mul(x, One);
}

fn field_multiply(a: Field, b: Field) -> Field {
  var x: Field = to_mont(a);
  var y: Field = to_mont(b);

  var z: Field;
  for (var i = 0; i < 1000; i++) {
    z = mont_mul(x, y);
  }

  var res: Field = from_mont(z);
  //var res = from_mont(mont_mul(to_mont(a), to_mont(b)));
  //var res = mont_mul(a, b);
  return res;
}

fn field_reduce(a: u256) -> Field {
  var reduction: Field = a;
  var a_gte_ALEO = gte(a, FIELD_ORDER);

  while (a_gte_ALEO) {
    reduction = u256_sub(reduction, FIELD_ORDER);
    a_gte_ALEO = gte(reduction, FIELD_ORDER);
  }

  return reduction;
}

//
/*
fn field_add(a: Field, b: Field) -> Field {
  var sum = u256_add(a, b);
  var result = field_reduce(sum);
  return result;
}
*/

fn field_sub(a: Field, b: Field) -> Field {
  var sub: Field;
  if (gte(a, b)) {
    sub = u256_sub(a, b);
  } else {
    var b_minus_a: Field = u256_sub(b, a);
    sub = u256_sub(FIELD_ORDER, b_minus_a);
  }

  return sub;
}

fn field_double(a: Field) -> Field {
  var double = u256_double(a);
  var result = field_reduce(double);
  return result;
}

//
/*
fn field_multiply(a: Field, b: Field) -> Field {
  var res: Field;
  for (var i = 0; i < 1000; i++) {
    res = field_multipl(a, b);
  }
  return res;
}*/

fn field_multipl(a: Field, b: Field) -> Field {
  var accumulator: Field = Field(
    array<u32, 8>(0, 0, 0, 0, 0, 0, 0, 0)
  );
  var newA: Field = a;
  var newB: Field = b;
  var count: u32 = 0u;

  while (gt(newB, U256_ZERO)) {
    if ((newB.components[7] & 1u) == 1u) {
      accumulator = u256_add(accumulator, newA);
      
      var accumulator_gte_ALEO = gte(accumulator, FIELD_ORDER);

      if (accumulator_gte_ALEO) {
        accumulator = u256_sub(accumulator, FIELD_ORDER);
      }
      
    }
    
    newA = u256_double(newA);
    newA = field_reduce(newA);
    newB = u256_right_shift(newB, 1u);
    count = count + 1u;
  }

  return accumulator;
}

fn field_pow(base: Field, exponent: Field) -> Field {
  if (equal(exponent, U256_ZERO)) { 
    return U256_ONE;
  }

  if (equal(exponent, U256_ONE)) { 
    return base;
  }

  var exp = exponent;
  var bse = base;
  var result: u256 = u256(
    array<u32, 8>(0, 0, 0, 0, 0, 0, 0, 1)
  );
  while (gt(exp, U256_ZERO)) {
    if (is_odd(exp)) {
      result = field_multiply(result, bse);
    }

    exp = u256_rs1(exp);
    bse = field_multiply(bse, bse);
  }

  return result;
}

fn field_pow_by_17(base: Field) -> Field {
  let bse = base;
  let base2 = field_multiply(bse, bse);
  let base4 = field_multiply(base2, base2);
  let base8 = field_multiply(base4, base4);
  let base16 = field_multiply(base8, base8);
  return field_multiply(base16, bse);
}

// assume that the input is NOT 0, as there's no inverse for 0
// this function implements the Guajardo Kumar Paar Pelzl (GKPP) algorithm,
// Algorithm 16 (BEA for inversion in Fp)
fn field_inverse(num: Field) -> Field {
  var u: Field = num;
  var v: u256 = FIELD_ORDER;
  var b: Field = U256_ONE;
  var c: Field = U256_ZERO;

  while (!equal(u, U256_ONE) && !equal(v, U256_ONE)) {
    while (is_even(u)) {
      // divide by 2
      u = u256_rs1(u);

      if (is_even(b)) {
        // divide by 2
        b = u256_rs1(b);
      } else {
        b = u256_add(b, FIELD_ORDER);
        b = u256_rs1(b);
      }
    }

    while (is_even(v)) {
      // divide by 2
      v = u256_rs1(v);
      if (is_even(c)) {
        c = u256_rs1(c);
      } else {
        c = u256_add(c, FIELD_ORDER);
        c = u256_rs1(c);
      }
    }

    if (gte(u, v)) {
      u = u256_sub(u, v);
      b = field_sub(b, c);
    } else {
      v = u256_sub(v, u);
      c = field_sub(c, b);
    }
  }

  if (equal(u, U256_ONE)) {
    return field_reduce(b);
  } else {
    return field_reduce(c);
  }
}

fn gen_field_reduce(a: u256, field_order: u256) -> Field {
  var reduction: Field = a;
  var a_gte_field_order = gte(a, field_order);

  while (a_gte_field_order) {
    reduction = u256_sub(reduction, field_order);
    a_gte_field_order = gte(reduction, field_order);
  }

  return reduction;
}

fn gen_field_add(a: Field, b: Field, field_order: Field) -> Field {
  var sum = u256_add(a, b);
  var result = gen_field_reduce(sum, field_order);
  return result;
}

fn gen_field_sub(a: Field, b: Field, field_order: Field) -> Field {
  var sub: Field;
  if (gte(a, b)) {
    sub = u256_sub(a, b);
  } else {
    var b_minus_a: Field = u256_sub(b, a);
    sub = u256_sub(field_order, b_minus_a);
  }

  return sub;
}

fn gen_field_multiply(a: Field, b: Field, field_order: u256) -> Field {
  var accumulator: Field = Field(
    array<u32, 8>(0, 0, 0, 0, 0, 0, 0, 0)
  );
  var newA: Field = a;
  var newB: Field = b;
  while (gt(newB, U256_ZERO)) {
    if ((newB.components[7] & 1u) == 1u) {
      accumulator = u256_add(accumulator, newA);
      if (gte(accumulator, field_order)) {
        accumulator = u256_sub(accumulator, field_order);
      }
    }
    newA = u256_double(newA);
    if (gte(newA, field_order)) {
      newA = u256_sub(newA, field_order);
    }
    newB = u256_rs1(newB);
  }

  return accumulator;
}

fn gen_field_pow(base: Field, exponent: Field, field_order: u256) -> Field { 
  if (equal(exponent, U256_ZERO)) { 
    return U256_ONE;
  }

  if (equal(exponent, U256_ONE)) { 
    return base;
  }

  var exp = exponent;
  var bse = base;
  var result: u256 = u256(
    array<u32, 8>(0, 0, 0, 0, 0, 0, 0, 1)
  );
  while (gt(exp, U256_ZERO)) { 
    if (is_odd(exp)) {
      result = gen_field_multiply(result, bse, field_order);
    }

    exp = u256_rs1(exp);
    bse = gen_field_multiply(bse, bse, field_order);
  }

  return result;
}
`