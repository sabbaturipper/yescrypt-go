// Copyright 2012-2020 The Go Authors. All rights reserved.
// Copyright 2024 Solar Designer. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package yescrypt implements the scrypt key derivation function as defined in
// Colin Percival's paper "Stronger Key Derivation via Sequential Memory-Hard
// Functions", as well as Solar Designer's yescrypt.

// yescrypt support sponsored by Sandfly Security https://sandflysecurity.com -
// Agentless Security for Linux

package yescrypt

import (
	"crypto/hmac"
	"crypto/sha256"
	"encoding/binary"
	"errors"
	"math/bits"

	"golang.org/x/crypto/pbkdf2"
)

const maxInt = int(^uint(0) >> 1)

// blockCopy copies n numbers from src into dst.
func blockCopy(dst, src []uint32, n int) {
	copy(dst, src[:n])
}

// blockXOR XORs numbers from dst with n numbers from src.
func blockXOR(dst, src []uint32, n int) {
	for i, v := range src[:n] {
		dst[i] ^= v
	}
}

// salsaXOR applies Salsa20/8 to the XOR of 16 numbers from tmp and in,
// and puts the result into both tmp and out.
func salsaXOR(tmp *[16]uint32, in, out []uint32, rounds int) {
	w0 := tmp[0] ^ in[0]
	w1 := tmp[1] ^ in[1]
	w2 := tmp[2] ^ in[2]
	w3 := tmp[3] ^ in[3]
	w4 := tmp[4] ^ in[4]
	w5 := tmp[5] ^ in[5]
	w6 := tmp[6] ^ in[6]
	w7 := tmp[7] ^ in[7]
	w8 := tmp[8] ^ in[8]
	w9 := tmp[9] ^ in[9]
	w10 := tmp[10] ^ in[10]
	w11 := tmp[11] ^ in[11]
	w12 := tmp[12] ^ in[12]
	w13 := tmp[13] ^ in[13]
	w14 := tmp[14] ^ in[14]
	w15 := tmp[15] ^ in[15]

	x0, x5, x10, x15, x4, x9, x14, x3 := w0, w1, w2, w3, w4, w5, w6, w7
	x8, x13, x2, x7, x12, x1, x6, x11 := w8, w9, w10, w11, w12, w13, w14, w15

	for i := 0; i < rounds; i += 2 {
		x4 ^= bits.RotateLeft32(x0+x12, 7)
		x8 ^= bits.RotateLeft32(x4+x0, 9)
		x12 ^= bits.RotateLeft32(x8+x4, 13)
		x0 ^= bits.RotateLeft32(x12+x8, 18)

		x9 ^= bits.RotateLeft32(x5+x1, 7)
		x13 ^= bits.RotateLeft32(x9+x5, 9)
		x1 ^= bits.RotateLeft32(x13+x9, 13)
		x5 ^= bits.RotateLeft32(x1+x13, 18)

		x14 ^= bits.RotateLeft32(x10+x6, 7)
		x2 ^= bits.RotateLeft32(x14+x10, 9)
		x6 ^= bits.RotateLeft32(x2+x14, 13)
		x10 ^= bits.RotateLeft32(x6+x2, 18)

		x3 ^= bits.RotateLeft32(x15+x11, 7)
		x7 ^= bits.RotateLeft32(x3+x15, 9)
		x11 ^= bits.RotateLeft32(x7+x3, 13)
		x15 ^= bits.RotateLeft32(x11+x7, 18)

		x1 ^= bits.RotateLeft32(x0+x3, 7)
		x2 ^= bits.RotateLeft32(x1+x0, 9)
		x3 ^= bits.RotateLeft32(x2+x1, 13)
		x0 ^= bits.RotateLeft32(x3+x2, 18)

		x6 ^= bits.RotateLeft32(x5+x4, 7)
		x7 ^= bits.RotateLeft32(x6+x5, 9)
		x4 ^= bits.RotateLeft32(x7+x6, 13)
		x5 ^= bits.RotateLeft32(x4+x7, 18)

		x11 ^= bits.RotateLeft32(x10+x9, 7)
		x8 ^= bits.RotateLeft32(x11+x10, 9)
		x9 ^= bits.RotateLeft32(x8+x11, 13)
		x10 ^= bits.RotateLeft32(x9+x8, 18)

		x12 ^= bits.RotateLeft32(x15+x14, 7)
		x13 ^= bits.RotateLeft32(x12+x15, 9)
		x14 ^= bits.RotateLeft32(x13+x12, 13)
		x15 ^= bits.RotateLeft32(x14+x13, 18)
	}
	w0 += x0
	w1 += x5
	w2 += x10
	w3 += x15
	w4 += x4
	w5 += x9
	w6 += x14
	w7 += x3
	w8 += x8
	w9 += x13
	w10 += x2
	w11 += x7
	w12 += x12
	w13 += x1
	w14 += x6
	w15 += x11

	out[0], tmp[0] = w0, w0
	out[1], tmp[1] = w1, w1
	out[2], tmp[2] = w2, w2
	out[3], tmp[3] = w3, w3
	out[4], tmp[4] = w4, w4
	out[5], tmp[5] = w5, w5
	out[6], tmp[6] = w6, w6
	out[7], tmp[7] = w7, w7
	out[8], tmp[8] = w8, w8
	out[9], tmp[9] = w9, w9
	out[10], tmp[10] = w10, w10
	out[11], tmp[11] = w11, w11
	out[12], tmp[12] = w12, w12
	out[13], tmp[13] = w13, w13
	out[14], tmp[14] = w14, w14
	out[15], tmp[15] = w15, w15
}

func blockMix(tmp *[16]uint32, in, out []uint32, r int) {
	blockCopy(tmp[:], in[(2*r-1)*16:], 16)
	for i := 0; i < 2*r; i += 2 {
		salsaXOR(tmp, in[i*16:], out[i*8:], 8)
		salsaXOR(tmp, in[i*16+16:], out[i*8+r*16:], 8)
	}
}

// These were tunable at design time, but they must meet certain constraints
const (
	PWXsimple = 2
	PWXgather = 4
	PWXrounds = 6
	Swidth    = 8
)

// Derived values.  These were never tunable on their own.
const (
	PWXbytes = PWXgather * PWXsimple * 8
	PWXwords = PWXbytes / 4
	Sbytes   = 3 * (1 << Swidth) * PWXsimple * 8
	Swords   = Sbytes / 4
	Smask    = (((1 << Swidth) - 1) * PWXsimple * 8)
)

type pwxformCtx struct {
	S0, S1, S2 []uint32
	w          uint32
}

func pwxform(X *[PWXwords]uint32, ctx *pwxformCtx) {
	S0, S1, S2, w := ctx.S0, ctx.S1, ctx.S2, ctx.w

	for i := 0; i < PWXrounds; i++ {
		for j := 0; j < PWXgather; j++ {
			xl := X[j*(PWXsimple*2)]
			xh := X[j*(PWXsimple*2)+1]
			p0 := S0[(xl&Smask)/4:]
			p1 := S1[(xh&Smask)/4:]
			for k := 0; k < PWXsimple*2; k += 2 {
				s0 := uint64(p0[k]) | uint64(p0[k+1])<<32
				s1 := uint64(p1[k]) | uint64(p1[k+1])<<32
				xl = X[j*(PWXsimple*2)+k]
				xh = X[j*(PWXsimple*2)+k+1]
				x := uint64(xh) * uint64(xl)
				x += s0
				x ^= s1
				X[j*(PWXsimple*2)+k] = uint32(x)
				X[j*(PWXsimple*2)+k+1] = uint32(x >> 32)

				if i != 0 && i != PWXrounds-1 {
					S2[w] = uint32(x)
					S2[w+1] = uint32(x >> 32)
					w += 2
				}
			}
		}
	}

	ctx.S0, ctx.S1, ctx.S2 = S2, S0, S1
	ctx.w = w & ((1<<Swidth)*PWXsimple*2 - 1)
}

func blockMixPwxform(X *[PWXwords]uint32, B []uint32, r int, ctx *pwxformCtx) {
	r1 := 128 * r / PWXbytes
	blockCopy(X[:], B[(r1-1)*PWXwords:], PWXwords)
	for i := 0; i < r1; i++ {
		blockXOR(X[:], B[i*PWXwords:], PWXwords)
		pwxform(X, ctx)
		blockCopy(B[i*PWXwords:], X[:], PWXwords)
	}
	i := (r1 - 1) * PWXbytes / 64
	*X = [PWXwords]uint32{} // We don't need the XOR, so set X to zeroes
	salsaXOR(X, B[i*PWXwords:], B[i*PWXwords:], 2)
}

func integer(b []uint32, r int) uint64 {
	j := (2*r - 1) * 16
	return uint64(b[j]) | uint64(b[j+13])<<32
}

func p2floor(x uint64) uint64 {
	for x&(x-1) != 0 {
		x &= x - 1
	}
	return x
}

func wrap(x, i uint64) uint64 {
	n := p2floor(i)
	return (x & (n - 1)) + (i - n)
}

func smix(b []byte, r, N, Nloop int, v, xy []uint32, ctx *pwxformCtx) {
	var tmp [16]uint32
	R := 32 * r
	x := xy
	y := xy[R:]

	j := 0
	for i := 0; i < R; i++ {
		x[i] = binary.LittleEndian.Uint32(b[(j & ^63)|((j*5)&63):])
		j += 4
	}
	if ctx != nil {
		for i := 0; i < N; i++ {
			blockCopy(v[i*R:], x, R)
			if i > 1 {
				j := int(wrap(integer(x, r), uint64(i)))
				blockXOR(x, v[j*R:], R)
			}
			blockMixPwxform(&tmp, x, r, ctx)
		}
		for i := 0; i < Nloop; i++ {
			j := int(integer(x, r) & uint64(N-1))
			blockXOR(x, v[j*R:], R)
			blockCopy(v[j*R:], x, R)
			blockMixPwxform(&tmp, x, r, ctx)
		}
	} else {
		for i := 0; i < N; i += 2 {
			blockCopy(v[i*R:], x, R)
			blockMix(&tmp, x, y, r)

			blockCopy(v[(i+1)*R:], y, R)
			blockMix(&tmp, y, x, r)
		}
		for i := 0; i < Nloop; i += 2 {
			j := int(integer(x, r) & uint64(N-1))
			blockXOR(x, v[j*R:], R)
			blockMix(&tmp, x, y, r)

			j = int(integer(y, r) & uint64(N-1))
			blockXOR(y, v[j*R:], R)
			blockMix(&tmp, y, x, r)
		}
	}
	j = 0
	for _, v := range x[:R] {
		binary.LittleEndian.PutUint32(b[(j & ^63)|((j*5)&63):], v)
		j += 4
	}
}

func smixYescrypt(b []byte, r, N int, v, xy []uint32, passwordSha256 []byte) {
	var ctx pwxformCtx
	var S [Swords]uint32
	smix(b, 1, Sbytes/128, 0, S[:], xy, nil)
	ctx.S2 = S[:]
	ctx.S1 = S[(1<<Swidth)*PWXsimple*2:]
	ctx.S0 = S[(1<<Swidth)*PWXsimple*2*2:]
	h := hmac.New(sha256.New, b[64*(2*r-1):])
	h.Write(passwordSha256)
	copy(passwordSha256, h.Sum(nil))
	smix(b, r, N, ((N+2)/3+1) & ^1, v, xy, &ctx)
}

func deriveKey(password, salt []byte, N, r, p, keyLen int, prehash []byte) ([]byte, error) {
	if N <= 1 || N&(N-1) != 0 {
		return nil, errors.New("(ye)scrypt: N must be > 1 and a power of 2")
	}
	if r <= 0 {
		return nil, errors.New("(ye)scrypt: r must be > 0")
	}
	if prehash != nil && p != 1 {
		return nil, errors.New("yescrypt: p must be 1")
	}
	if p <= 0 {
		return nil, errors.New("scrypt: p must be > 0")
	}
	if uint64(r)*uint64(p) >= 1<<30 || r > maxInt/128/p || r > maxInt/256 || N > maxInt/128/r {
		return nil, errors.New("(ye)scrypt: parameters are too large")
	}

	ppassword := &password
	if prehash != nil {
		h := hmac.New(sha256.New, prehash)
		h.Write(password)
		passwordSha256 := h.Sum(nil)
		ppassword = &passwordSha256
	}

	b := pbkdf2.Key(*ppassword, salt, 1, p*128*r, sha256.New)

	v := make([]uint32, 32*N*r)
	if prehash != nil {
		xy := make([]uint32, 32*max(r, 2))
		copy(*ppassword, b[:32])
		smixYescrypt(b, r, N, v, xy, *ppassword)
	} else {
		xy := make([]uint32, 64*r)
		for i := 0; i < p; i++ {
			smix(b[i*128*r:], r, N, N, v, xy, nil)
		}
	}

	key := pbkdf2.Key(*ppassword, b, 1, max(keyLen, 32), sha256.New)

	if len(prehash) == 8 {
		h1 := hmac.New(sha256.New, key[:32])
		h1.Write([]byte("Client Key"))
		h2 := sha256.New()
		h2.Write(h1.Sum(nil))
		copy(key, h2.Sum(nil))
	}

	return key[:keyLen], nil
}

// Classic scrypt
//
// ScryptKey implements classic scrypt (not yescrypt).  It is compatible with
// the x/crypto scrypt module's Key.
//
// It derives a key from the password, salt and cost parameters, returning a
// byte slice of length keyLen that can be used as cryptographic key.
//
// N is a CPU/memory cost parameter, which must be a power of two greater than 1.
// r and p must satisfy r * p < 2³⁰. If the parameters do not satisfy the
// limits, the function returns a nil byte slice and an error.
//
// For example, you can get a derived key for e.g. AES-256 (which needs a
// 32-byte key) by doing:
//
//	dk, err := yescrypt.ScryptKey([]byte("some password"), salt, 32768, 8, 1, 32)
//
// The recommended parameters for interactive logins as of 2017 are N=32768, r=8
// and p=1. The parameters N, r, and p should be increased as memory latency and
// CPU parallelism increases; consider setting N to the highest power of 2 you
// can derive within 100 milliseconds. Remember to get a good random salt.
func ScryptKey(password, salt []byte, N, r, p, keyLen int) ([]byte, error) {
	return deriveKey(password, salt, N, r, p, keyLen, nil)
}

// Native yescrypt
//
// Key is similar to ScryptKey, but computes native yescrypt assuming
// reference yescrypt's current default flags (as of yescrypt 1.1.0), p=1
// (which it currently requires), t=0, and no ROM.  Example usage:
//
//	dk, err := yescrypt.Key([]byte("some password"), salt, 32768, 8, 1, 32)
//
// The set of parameters accepted by Key will likely change in future versions
// of this Go module to support more yescrypt functionality.
func Key(password, salt []byte, N, r, p, keyLen int) ([]byte, error) {
	ppassword := &password
	if p >= 1 && N/p >= 0x100 && N/p*r >= 0x20000 {
		passwordSha256, err := deriveKey(*ppassword, salt, N>>6, r, p, 32, []byte("yescrypt-prehash"))
		if err != nil {
			return nil, err
		}
		ppassword = &passwordSha256
	}
	return deriveKey(*ppassword, salt, N, r, p, keyLen, []byte("yescrypt"))
}
