val _ = OS.Process.exit
        (LoadH0.wrappergen (CommandLine.name (),
                            CommandLine.arguments ()))
