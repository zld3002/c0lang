public class _l_rand
{
	public class _s_rand
	{
		public int seed;
	}

	public static P<_s_rand> init_rand (int seed)
	{
		P<_s_rand> gen = new P<_s_rand>(new _s_rand());
		gen.value.seed = seed;
		return gen;
	}

	public static int rand (P<_s_rand> gen)
	{
		gen.value.seed = gen.value.seed * 1664525 + 1013904223;
		return gen.value.seed;
	}
}
