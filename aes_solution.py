import binascii
import filecmp
import time
from collections import deque
from BitVector import *

BITS = 128              # AES-version
ROW = 4                 # Matrix row
COL = BITS // 32        # Matrix column
KEY_CHARS = BITS // 8   # Number of characters in a key
KEY_LEN = BITS // 32    # Length of the key in 32-bit words

TEXT_CHARS = BITS // 8  # Number of characters in plain text
ROUND = BITS // 32 + 7  # Total rounds in AES
AES_modulus = BitVector(bitstring='100011011')  # 0x11B

INPUT_FILE = "compress_me.txt"
OUTPUT_FILE = "out"

Sbox = [0] * 256
InvSbox = [0] * 256
round_const = [BitVector(size=32)] * ROUND  # round constants for key scheduling

space_padding = 0  # Extra space padding added to plain text

# Utility matrix used in encryption & decryption stages
Mixer = [
    [BitVector(hexstring="02"), BitVector(hexstring="03"), BitVector(hexstring="01"), BitVector(hexstring="01")],
    [BitVector(hexstring="01"), BitVector(hexstring="02"), BitVector(hexstring="03"), BitVector(hexstring="01")],
    [BitVector(hexstring="01"), BitVector(hexstring="01"), BitVector(hexstring="02"), BitVector(hexstring="03")],
    [BitVector(hexstring="03"), BitVector(hexstring="01"), BitVector(hexstring="01"), BitVector(hexstring="02")]
]

InvMixer = [
    [BitVector(hexstring="0E"), BitVector(hexstring="0B"), BitVector(hexstring="0D"), BitVector(hexstring="09")],
    [BitVector(hexstring="09"), BitVector(hexstring="0E"), BitVector(hexstring="0B"), BitVector(hexstring="0D")],
    [BitVector(hexstring="0D"), BitVector(hexstring="09"), BitVector(hexstring="0E"), BitVector(hexstring="0B")],
    [BitVector(hexstring="0B"), BitVector(hexstring="0D"), BitVector(hexstring="09"), BitVector(hexstring="0E")]
]


# Matrix class to perform operations on BitVector matrix
class Matrix:
    matrix = [[BitVector(hexstring="")] * COL for _ in range(ROW)]

    # constructor takes blocks of input plain text and constructs matrix in column major order
    def __init__(self, text):
        for j in range(COL):
            for i in range(ROW):
                self.matrix[i][j] = BitVector(textstring=text[j * ROW + i])

    # prints matrix in hex
    def print(self):
        for i in range(ROW):
            for j in range(COL):
                print(self.matrix[i][j].getHexStringFromBitVector(), end=' ')
            print()
        print()

    # adds round key by performing xor operation
    def add_round_key(self, round_key):
        cnt = 0
        for j in range(COL):
            for i in range(ROW):
                self.matrix[i][j] ^= round_key[cnt:cnt + 8]
                cnt += 8

    # substitutes matrix elements with Sbox elements if encryption_mode is True,
    # otherwise replaces with InvSbox
    def substitute_bytes(self, encryption_mode):
        for i in range(ROW):
            for j in range(COL):
                int_val = self.matrix[i][j].intValue()
                int_val = Sbox[int_val] if encryption_mode is True else InvSbox[int_val]
                self.matrix[i][j] = BitVector(intVal=int_val, size=8)

    # shifts matrix according to AES algorithm
    # cyclic left shift for encryption
    # cyclic right shift for decryption
    def shift_rows(self, encryption_mode):
        for i in range(ROW):
            items = deque(self.matrix[i])
            items.rotate(i * (-1 if encryption_mode is True else 1))
            for j in range(COL):
                self.matrix[i][j] = items[j]

    # Performs matrix multiplication in finite field
    def mix_columns(self, encryption_mode):
        new_mat = [[BitVector(intVal=0, size=8)] * COL for _ in range(ROW)]
        mixer = Mixer if encryption_mode is True else InvMixer
        for i in range(ROW):
            for j in range(COL):
                for k in range(ROW):
                    new_mat[i][j] ^= mixer[i][k].gf_multiply_modular(self.matrix[k][j], AES_modulus, 8)
        self.matrix = new_mat

    # returns the hex form of the matrix in column major order
    def get_hex_form(self):
        ret_text = ""
        for j in range(COL):
            for i in range(ROW):
                ret_text += self.matrix[i][j].getHexStringFromBitVector()
        return ret_text


"""
Adjusts input hex text/file to be a multiple of TEXT_LEN padding with spaces.
Adds an extra TEXT_LEN block to indicate the number of added spaces in the previous block.

Parameter
----------
text: str
    Input text/file in hex

Returns
--------
str
    formatted hex text/file

"""


def process_plain_text(text):
    global space_padding
    len_now = len(text)
    new_len = ((len_now - 1) // TEXT_CHARS + 1) * TEXT_CHARS  # making text_len multiple of TEXT_CHARS by taking ceiling
    text = text.ljust(new_len)  # padding with spaces
    space_padding = new_len - len_now
    return text


"""
Generating round constants for key scheduling
Link: https://en.wikipedia.org/wiki/AES_key_schedule

The round constant round_const[i] for round i of the key expansion is the 32-bit word: [rc_i  00  00  00]
"""


def generate_round_constants():
    rc = [0] * ROUND
    rc[1] = 1
    for i in range(2, ROUND):
        rc[i] = 2 * rc[i - 1]
        rc[i] ^= int("11B", 16) if rc[i - 1] >= int("80", 16) else 0

    for i in range(1, ROUND):
        # left shifting to generate [rc_i  00  00  00] in hex
        round_const[i] = BitVector(intVal=rc[i] * (1 << 24), size=32)
    return round_const


"""
Generates Rijndael S-Box and Inverse S-Box Matrices
Link: https://en.wikipedia.org/wiki/Rijndael_S-box 

Formula = b ^ (b <<< 1) ^ (b <<< 2) ^ (b <<< 3) ^ (b <<< 4) ^ hex(63)
here, b = multiplicative inverse of a bit vector in the Galois Field GF(2^n) with respect to a modulus polynomial

"""


def generate_sbox():
    Sbox[0] = 0x63  # No MI. for 0
    for i in range(1, 256):
        b = BitVector(intVal=i, size=8).gf_MI(AES_modulus, 8)
        int_val = b.intValue()
        for j in range(1, 5):
            b ^= (BitVector(intVal=int_val, size=8) << j)
        b ^= BitVector(hexstring="63")
        Sbox[i] = b.intValue()
        InvSbox[b.intValue()] = i


# Generate all necessary matrices for AES encryption & decryption
def generate_matrices():
    generate_sbox()
    generate_round_constants()


"""
Utility function to perform subWord() in key scheduling algorithm

Parameter
----------
key: Bitvector
    A 32-bit word

Returns
--------
BitVector
    Substituted word from S-Box
 
"""


def substitute_word(key):
    sub_word = BitVector(size=32)
    for i in range(4):
        sbox_id = key[i * 8: (i + 1) * 8].intValue()  # taking 8 bits at a time
        sub_word << 8  # shifting and concatenating 8 bits
        sub_word |= BitVector(intVal=Sbox[sbox_id], size=32)
    return sub_word


"""
Generates round keys using the key schedule algorithm
Link: https://en.wikipedia.org/wiki/AES_key_schedule

Parameter
-----------
key : str
    Encryption & decryption key of length KEY_LEN
    
Returns
--------
list
    a list of BitVectors: The round keys
"""


def generate_round_keys(key):
    init_key = BitVector(textstring=key)
    word_keys = []

    for i in range(0, ROUND * KEY_LEN):  # Generate all words required for all rounds
        if i < KEY_LEN:
            word_keys.append(init_key[i * 32: (i + 1) * 32])
        else:
            new_word = word_keys[i - 1].deep_copy()
            if i % KEY_LEN == 0:
                new_word = substitute_word(new_word << 8) ^ round_const[i // KEY_LEN]
            elif KEY_LEN > 6 and i % KEY_LEN == 4:
                new_word = substitute_word(new_word)
            word_keys.append(new_word ^ word_keys[i - KEY_LEN])

    round_keys = [BitVector(hexstring="")] * ROUND  # Concatenating every KEY_LEN words to form a round_key
    for i in range(ROUND):
        round_key = ""
        for j in range(KEY_LEN):
            round_key += word_keys[i * KEY_LEN + j].getHexStringFromBitVector()
        round_keys[i] = BitVector(hexstring=round_key)
    return round_keys


"""
Converts a BitVector to a 4x4 matrix BitVector in column major order
Parameter
----------
bit_vec: BitVector

Returns
--------
A 4x4 BitVector array
"""


def bitvector_to_matrix(bit_vec):
    bits_per_entry = len(bit_vec) // 16
    mat = [[BitVector(hexstring="") for _ in range(ROW)] for _ in range(ROW)]
    for j in range(ROW):
        for i in range(ROW):
            mat[i][j] = bit_vec[:bits_per_entry]
            bit_vec = bit_vec[bits_per_entry:]
    return mat


"""
Adds round key to mat by performing xor operation
Parameters
-----------
mat: 4x4 BitVector
round_mat : 4x4 BitVector
 
Returns
--------
Resulting matrix after adding round key
"""


def add_round_key(mat, round_mat):
    for i in range(ROW):
        for j in range(ROW):
            mat[i][j] ^= round_mat[i][j]
    return mat


"""
Decrypts cipher text with round_keys

Parameter
------------
text: str
    ciphered string in hex string
round_keys: list of BitVector 
    round keys for all rounds

Returns
---------
str
    Deciphered plain text 
"""


def decrypt(text, round_keys):
    deciphered_text = ""
    text = bytes.fromhex(text).decode('latin-1')

    turn = len(text) // TEXT_CHARS  # Number of chunks to decipher at a time
    for i in range(turn):
        if i % 10 == 0:
            print("Decrypting block: ", i + 1)
        matrix = Matrix(text[i * TEXT_CHARS:(i + 1) * TEXT_CHARS])
        for j in range(ROUND - 1, 0, -1):
            matrix.add_round_key(round_keys[j])
            if j != ROUND - 1:
                matrix.mix_columns(encryption_mode=False)
            matrix.shift_rows(encryption_mode=False)
            matrix.substitute_bytes(encryption_mode=False)

        matrix.add_round_key(round_keys[0])
        deciphered_text += matrix.get_hex_form()
    deciphered_text = bytes.fromhex(deciphered_text).decode('latin-1')
    deciphered_text = deciphered_text[:len(deciphered_text) - space_padding]    # trimming extra paddings
    return deciphered_text


"""
Encrypts input plain text with round_keys
Link: https://en.wikipedia.org/wiki/Advanced_Encryption_Standard

Parameter
------------
text: str
    Input text whose length is a multiple of TEXT_CHARS
round_keys: BitVector[] 
    round keys for all rounds

Returns
---------
str
    ciphered text in hex 
"""


def encrypt(text, round_keys):
    cypher_text = ""
    turn = len(text) // TEXT_CHARS  # Number of chunks input text is divided into
    print("Total input block(s):", turn)
    print("--------------------------")

    for i in range(turn):  # process 128 bits at a time (AES-128)
        if i % 10 == 0:  # For debugging
            print("Encrypting block: ", i + 1)
        matrix = Matrix(text[i * TEXT_CHARS:(i + 1) * TEXT_CHARS])  # create 4x4 matrix (AES-128)
        matrix.add_round_key(round_keys[0])

        for j in range(1, ROUND):
            matrix.substitute_bytes(encryption_mode=True)
            matrix.shift_rows(encryption_mode=True)
            if j != ROUND - 1:  # skip mixing columns in the last round
                matrix.mix_columns(encryption_mode=True)
            matrix.add_round_key(round_keys[j])
        cypher_text += matrix.get_hex_form()
    print()
    return cypher_text


def main():
    generate_matrices()  # pre-calculations
    start_time = time.time()

    key = "BUET CSE16 Batch"
    key = key.ljust(KEY_CHARS, '0')[:KEY_CHARS]  # making length of key to KEY_CHARS

    # Round key generation
    round_keys = generate_round_keys(key)
    key_scheduling_time = time.time() - start_time
    start_time = time.time()

    # Text Encryption
    text = "WillGraduateSoon"

    # for file Encryption
    # with open(INPUT_FILE, 'rb') as f:
    #     text = bytes.hex(f.read())
    # text = bytes.fromhex(text).decode('latin-1')

    text = process_plain_text(text)  # input padding
    ciphered_text = encrypt(text, round_keys)  # encryption
    encryption_time = time.time() - start_time
    start_time = time.time()

    deciphered_text = decrypt(ciphered_text, round_keys)  # decryption
    decryption_time = time.time() - start_time

    # for file decryption
    # with open(OUTPUT_FILE, 'wb') as f:
    #     f.write(bytes(deciphered_text, 'latin-1'))

    print("\n\n---------------------Execution Status--------------------\n\n")
    print("File Encryption Decryption status: ", filecmp.cmp(INPUT_FILE, OUTPUT_FILE))
    print("Key:")
    print(key, "[IN ASCII]")
    print(key.encode("latin-1").hex(), "[In HEX]\n")

    print("Plain Text:")
    print(text, "[In ASCII]")
    print(text.encode("latin-1").hex(), "[In HEX]\n")

    print("Cipher Text:")
    print(ciphered_text, "[In HEX]")
    print(bytes.fromhex(ciphered_text).decode('latin-1'), "[In ASCII]\n")

    print("Deciphered Text:")
    print(deciphered_text.encode("latin-1").hex(), "[In HEX]")
    print(deciphered_text, "[In ASCII]\n")

    print("Execution Time:")
    print("Key Scheduling:", key_scheduling_time, "seconds")
    print("Encryption Time:", encryption_time, "seconds")
    print("Decryption Time:", decryption_time, "seconds")


main()
