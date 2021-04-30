// Copyright 2020 CoreOS, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use anyhow::{anyhow, Context, Result};
use std::process::Command;

use libcoreinst::install::*;
use libcoreinst::runcmd;

use crate::cmdline::*;
use crate::rootmap::get_boot_mount_from_cmdline_args;

pub fn kargs(config: &KargsConfig) -> Result<()> {
    if let Some(ref orig_options) = config.override_options {
        modify_and_print(config, orig_options.trim()).context("modifying options")?;
    } else {
        // the unwrap() here is safe because we checked in cmdline that one of them must be provided
        let mount =
            get_boot_mount_from_cmdline_args(&config.boot_mount, &config.boot_device)?.unwrap();
        let changed = visit_bls_entry_options(mount.mountpoint(), |orig_options: &str| {
            modify_and_print(config, orig_options)
        })
        .context("visiting BLS options")?;

        if changed && cfg!(target_arch = "s390x") {
            runcmd!("zipl", "--target", mount.mountpoint())?;
        }
    }

    Ok(())
}

fn modify_and_print(config: &KargsConfig, orig_options: &str) -> Result<Option<String>> {
    let new_options = bls_entry_options_delete_and_append_kargs(
        orig_options,
        config.delete_kargs.as_slice(),
        config.append_kargs.as_slice(),
        config.append_kargs_if_missing.as_slice(),
    )?;

    // we always print the final kargs
    if let Some(ref options) = new_options {
        println!("{}", options);
        if options != orig_options {
            if let Some(ref path) = config.create_if_changed {
                std::fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(path)
                    .with_context(|| format!("creating {}", path))?;
            }
        }
    } else {
        println!("{}", orig_options);
    }

    Ok(new_options)
}
