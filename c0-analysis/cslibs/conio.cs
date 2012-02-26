
public class _l_conio
{
	public static void print(string s)
	{
		System.Console.Write(s);
	}

	public static void println (string s)
	{
		System.Console.WriteLine(s);
	}

	public static void printint(int n)
	{
		System.Console.Write(n);
	}

	public static void printbool(bool b)
	{
		System.Console.Write(b);
	}

	public static void printchar(char c)
	{
		System.Console.Write(c);
	}

	public static string readline()
	{
		return System.Console.ReadLine();
	}

	public static void error(string s)
	{
		C0Program.assert(false, s);
	}
}
