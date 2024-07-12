# N.B. Only the X86 NCG and LLVM backends support SIMD operations for now.
setTestOpts([ unless(arch('x86_64'), only_ways(llvm_ways))
            , unless(have_cpu_feature('sse4_1') or have_cpu_feature('avx'), skip)
            , when(have_cpu_feature('sse4_1'), extra_hc_opts('-msse4'))
            , when(have_cpu_feature('sse4_2'), extra_hc_opts('-msse4.2'))
            , when(have_cpu_feature('avx'), extra_hc_opts('-mavx'))
            , when(have_cpu_feature('avx2'), extra_hc_opts('-mavx2'))
            , when(have_cpu_feature('avx512f'), extra_hc_opts('-mavx512f'))
            , when(unregisterised(), skip)
            , when(arch('wasm32'), skip)
            , js_skip
            ])

test('simd000', [], compile_and_run, [''])
test('simd001', [], compile_and_run, [''])
test('simd002', [], compile_and_run, [''])
test('simd003', [], compile_and_run, [''])
test('simd004', [], compile_and_run, ['-O2'])
test('simd005', [], compile_and_run, [''])
test('simd006', [], compile_and_run, [''])
test('simd007', [], compile_and_run, [''])
test('simd008', [], compile_and_run, [''])
test('simd009', [ req_th
                , extra_files(['Simd009b.hs', 'Simd009c.hs'])
                , unless(have_cpu_feature('avx'), skip)
                ]
              , multimod_compile_and_run, ['simd009', ''])
test('simd010', [], compile_and_run, [''])

test('T25062_V16', [], compile_and_run, [''])
test('T25062_V32', [ unless(have_cpu_feature('avx2'), skip)
                   , only_ways(llvm_ways)
                   ]
                 , compile_and_run, [''])
test('T25062_V64', [ unless(have_cpu_feature('avx512f'), skip)
                   , only_ways(llvm_ways)
                   ]
                 , compile_and_run, [''])
