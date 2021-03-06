/*
* Blake2b
* (C) 2016 cynecx
*
* Botan is released under the Simplified BSD License (see license.txt)
*/

#ifndef BOTAN_BLAKE2B_H__
#define BOTAN_BLAKE2B_H__

#include <botan/hash.h>
#include <string>
#include <memory>

namespace Botan {

enum blake2b_constant {
  BLAKE2B_BLOCKBYTES = 128,
  BLAKE2B_OUTBYTES   = 64,
  BLAKE2B_IVU64COUNT = 8
};

/**
* BLAKE2B
*/
class BOTAN_DLL Blake2b final : public HashFunction
   {
   public:
      /**
      * @param output_bits the output size of Blake2b in bits
      */
      explicit Blake2b(size_t output_bits = 512);

      size_t hash_block_size() const override { return BLAKE2B_BLOCKBYTES; }
      size_t output_length() const override { return m_output_bits / 8; }

      static Blake2b* make(const Spec& spec);

      HashFunction* clone() const override;
      std::string name() const override;
      void clear() override;

   private:
      void add_data(const byte input[], size_t length) override;
      void final_result(byte out[]) override;

      inline void state_init();
      inline void increment_counter(const u64bit inc);
      void compress(bool lastblock = false);

      size_t m_output_bits;

      secure_vector<byte> m_buffer;
      size_t m_buflen;

      secure_vector<u64bit> m_H;
      u64bit m_T[2];
      u64bit m_F[2];
   };

}

#endif
