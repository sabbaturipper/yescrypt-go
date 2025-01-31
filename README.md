Go implementation of scrypt and yescrypt key derivation and password hashing
functions, which have their homepages at:
https://www.tarsnap.com/scrypt.html
https://www.openwall.com/yescrypt

This Go implementation of scrypt was created in 2012 by Dmitry Chestnykh, who
has since contributed it to the official Go x/crypto repository where it's now
maintained by the Go authors.  This tree is based on Dmitry's with all x/crypto
changes as of mid-2024 added.  The implementation of yescrypt was added in 2024
by Solar Designer, sponsored by Sandfly Security https://sandflysecurity.com -
Agentless Security for Linux.

INSTALLATION

    $ go get github.com/openwall/yescrypt-go

PACKAGE
    import "github.com/openwall/yescrypt-go"

    Package yescrypt implements the scrypt key derivation function as defined
    in Colin Percival's paper "Stronger Key Derivation via Sequential
    Memory-Hard Functions", as well as Solar Designer's yescrypt.

FUNCTIONS

func ScryptKey(password, salt []byte, N, r, p, keyLen int) ([]byte, error)

    ScryptKey implements classic scrypt (not yescrypt).  It is compatible with
    the x/crypto scrypt module's Key.

    It derives a key from the password, salt and cost parameters, returning a
    byte slice of length keyLen that can be used as cryptographic key.

    N is a CPU/memory cost parameter, must be a power of two greater than 1.
    r and p must satisfy r * p < 2³⁰. If the parameters do not satisfy the
    limits, the function returns a nil byte slice and an error.

    For example, you can get a derived key for e.g. AES-256 (which needs a
    32-byte key) by doing:

	dk, err := yescrypt.ScryptKey([]byte("some password"), salt, 32768, 8, 1, 32)

The recommended parameters for interactive logins as of 2017 are N=32768, r=8
and p=1. The parameters N, r, and p should be increased as memory latency and
CPU parallelism increases; consider setting N to the highest power of 2 you
can derive within 100 milliseconds. Remember to get a good random salt.

func Key(password, salt []byte, N, r, p, keyLen int) ([]byte, error)

    Key is similar to ScryptKey, but computes native yescrypt assuming
    reference yescrypt's current default flags (as of yescrypt 1.1.0), p=1
    (which it currently requires), t=0, and no ROM.  Example usage:

	dk, err := yescrypt.Key([]byte("some password"), salt, 32768, 8, 1, 32)

    The set of parameters accepted by Key will likely change in future versions
    of this Go module to support more yescrypt functionality.

func Hash(password, setting []byte) ([]byte, error)

    Computes yescrypt hash encoding given the password and existing yescrypt
    setting or full hash encoding.  The salt and other parameters are decoded
    from setting.  Currently supports (only a little more than) the subset of
    yescrypt parameters that libxcrypt can generate (as of libxcrypt 4.4.36).

KEYWORDS

    go, golang, scrypt, yescrypt, kdf, hash, password
