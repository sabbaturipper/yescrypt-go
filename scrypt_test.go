// Copyright 2012 Dmitry Chestnykh. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package scrypt

import (
	"bytes"
	"testing"
)

type testVector struct {
	password string
	salt     string
	N, r, p  int
	output   []byte
}

var good = []testVector{
	{
		"password",
		"salt",
		2, 10, 10,
		[]byte{
			0x48, 0x2c, 0x85, 0x8e, 0x22, 0x90, 0x55, 0xe6, 0x2f,
			0x41, 0xe0, 0xec, 0x81, 0x9a, 0x5e, 0xe1, 0x8b, 0xdb,
			0x87, 0x25, 0x1a, 0x53, 0x4f, 0x75, 0xac, 0xd9, 0x5a,
			0xc5, 0xe5, 0xa, 0xa1, 0x5f,
		},
	},
	{
		"password",
		"salt",
		16, 100, 100,
		[]byte{
			0x88, 0xbd, 0x5e, 0xdb, 0x52, 0xd1, 0xdd, 0x0, 0x18,
			0x87, 0x72, 0xad, 0x36, 0x17, 0x12, 0x90, 0x22, 0x4e,
			0x74, 0x82, 0x95, 0x25, 0xb1, 0x8d, 0x73, 0x23, 0xa5,
			0x7f, 0x91, 0x96, 0x3c, 0x37,
		},
	},
	{
		"this is a long \000 password",
		"and this is a long \000 salt",
		16384, 8, 1,
		[]byte{
			0xc3, 0xf1, 0x82, 0xee, 0x2d, 0xec, 0x84, 0x6e, 0x70,
			0xa6, 0x94, 0x2f, 0xb5, 0x29, 0x98, 0x5a, 0x3a, 0x9,
			0x76, 0x5e, 0xf0, 0x4c, 0x61, 0x29, 0x23, 0xb1, 0x7f,
			0x18, 0x55, 0x5a, 0x37, 0x7, 0x6d, 0xeb, 0x2b, 0x98,
			0x30, 0xd6, 0x9d, 0xe5, 0x49, 0x26, 0x51, 0xe4, 0x50,
			0x6a, 0xe5, 0x77, 0x6d, 0x96, 0xd4, 0xf, 0x67, 0xaa,
			0xee, 0x37, 0xe1, 0x77, 0x7b, 0x8a, 0xd5, 0xc3, 0x11,
			0x14, 0x32, 0xbb, 0x3b, 0x6f, 0x7e, 0x12, 0x64, 0x40,
			0x18, 0x79, 0xe6, 0x41, 0xae,
		},
	},
	{
		"p",
		"s",
		2, 1, 1,
		[]byte{
			0x48, 0xb0, 0xd2, 0xa8, 0xa3, 0x27, 0x26, 0x11, 0x98,
			0x4c, 0x50, 0xeb, 0xd6, 0x30, 0xaf, 0x52,
		},
	},
}

var bad = []testVector{
	{"p", "s", 0, 1, 1, nil},                    // N == 0
	{"p", "s", 1, 1, 1, nil},                    // N == 1
	{"p", "s", 7, 8, 1, nil},                    // N is not power of 2
	{"p", "s", 16, maxInt / 2, maxInt / 2, nil}, // p * r too large
}

func TestKey(t *testing.T) {
	for _, v := range good {
		k, err := Key([]byte(v.password), []byte(v.salt), v.N, v.r, v.p, len(v.output))
		if err != nil {
			t.Errorf("got unexpected error: %s", err)
		}
		if !bytes.Equal(k, v.output) {
			t.Errorf("expected %x, got %x", v.output, k)
		}
	}
	for _, v := range bad {
		_, err := Key([]byte(v.password), []byte(v.salt), v.N, v.r, v.p, 32)
		if err == nil {
			t.Errorf("expected error, got nil")
		}
	}
}

func BenchmarkKey(b *testing.B) {
	for i := 0; i < b.N; i++ {
		Key([]byte("password"), []byte("salt"), 16384, 8, 1, 64)
	}
}
