!macro customUnInstall
  ; Remove startup registrations created by Electron's app.setLoginItemSettings.
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine Desktop"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine.exe"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "dev.rmkcet.shine"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "rmkcet-shine-desktop"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Run" "rmkcet_shine_app"

  ; Defensive cleanup for installs that may have been elevated or manually moved.
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine"
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine Desktop"
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "RMKCET Shine.exe"
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "dev.rmkcet.shine"
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "rmkcet-shine-desktop"
  DeleteRegValue HKLM "Software\Microsoft\Windows\CurrentVersion\Run" "rmkcet_shine_app"

  ; Windows tracks startup approval state separately from the Run key.
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "RMKCET Shine"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "RMKCET Shine Desktop"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "RMKCET Shine.exe"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "dev.rmkcet.shine"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "rmkcet-shine-desktop"
  DeleteRegValue HKCU "Software\Microsoft\Windows\CurrentVersion\Explorer\StartupApproved\Run" "rmkcet_shine_app"

  ; Also remove any Startup-folder shortcuts left by older installer experiments.
  Delete "$SMSTARTUP\RMKCET Shine.lnk"
  Delete "$SMSTARTUP\RMKCET Shine Desktop.lnk"
  Delete "$SMSTARTUP\rmkcet-shine-desktop.lnk"
  Delete "$SMSTARTUP\rmkcet_shine_app.lnk"
!macroend
