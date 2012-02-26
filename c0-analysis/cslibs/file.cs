using System.IO;

public class _l_file
{

	public class _s_file
	{
		public TextReader tr;
		public bool was_closed;
	}

	public static P<_s_file> file_read(string path)
	{
		_s_file file = new _s_file();
		try{
			file.tr = new StreamReader(path);
		}
		catch (System.Exception) {
			C0Program.assert(false, "Error opening file");
		}
		if (file.tr == null)
			System.Environment.Exit(-1);
		return new P<_s_file>(file);
	}

	public static void file_close (P<_s_file> f)
	{
		if (f.value.was_closed)
			C0Program.assert(false, "Double close on a file");

		f.value.was_closed = true;
		f.value.tr.Close();
	}

	public static bool file_eof (P<_s_file> f)
	{
		return (f.value.tr.Peek() == -1);
	}

	public static string file_readline(P<_s_file> f)
	{
		return f.value.tr.ReadLine();
	}
}
